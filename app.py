from __future__ import annotations

import csv
import hmac
import json
import os
import shutil
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Dict, Optional
from urllib.parse import quote

from flask import (
    Flask,
    abort,
    flash,
    redirect,
    render_template,
    request,
    send_file,
    send_from_directory,
    session,
    url_for,
)
from werkzeug.utils import secure_filename

# ----------------------------
# Paths (Render Disk ready)
# ----------------------------
BASE_DIR = Path(__file__).resolve().parent

DATA_DIR = Path(os.environ.get("DATA_DIR", str(BASE_DIR / "data"))).resolve()
UPLOADS_DIR = Path(os.environ.get("UPLOADS_DIR", str(BASE_DIR / "uploads"))).resolve()

DATA_DIR.mkdir(parents=True, exist_ok=True)
UPLOADS_DIR.mkdir(parents=True, exist_ok=True)

SUBMISSIONS_CSV = DATA_DIR / "submissions.csv"
COMMENTS_CSV = DATA_DIR / "comments.csv"
AGENT_PROFILE_JSON = DATA_DIR / "agent_profile.json"
AGENT_PROFILE_SID = "_agent_profile"
AGENT_OFFER_PASSWORD_FILE = DATA_DIR / "agent_offer_password.txt"
DEFAULT_AGENT_OFFER_PASSWORD = "Free"

# ----------------------------
# Upload policy
# ----------------------------
ALLOWED_EXT = {"jpg", "jpeg", "png", "webp", "gif", "heic", "heif"}
# Only these formats are reliably rendered by normal browsers inside <img>.
# HEIC/HEIF can be uploaded, but most browsers will not preview them without conversion.
BROWSER_IMAGE_EXT = {"jpg", "jpeg", "png", "webp", "gif"}
MAX_FILES = int(os.environ.get("MAX_FILES", "5"))
MAX_TOTAL_MB = int(os.environ.get("MAX_TOTAL_MB", "25"))  # whole request cap
MAX_FILE_MB = int(os.environ.get("MAX_FILE_MB", "10"))    # per photo cap
COMMENT_CONTACT_MAX = int(os.environ.get("COMMENT_CONTACT_MAX", "120"))
COMMENT_MESSAGE_MAX = int(os.environ.get("COMMENT_MESSAGE_MAX", "2000"))

app = Flask(__name__, static_folder="static", static_url_path="/static")

@app.template_filter('is_numeric')
def is_numeric_filter(value) -> bool:
    """Return True if the string looks like a plain number (after removing separators)."""
    if value is None:
        return False
    s = str(value).strip()
    if not s:
        return False
    # remove common thousands separators and spaces
    for ch in (' ', '\u00a0', ',', '.', '_'):
        s = s.replace(ch, '')
    return s.isdigit()


@app.template_filter('format_price')
def format_price_filter(value) -> str:
    """Display numeric prices with spaces: 12000000 -> 12 000 000."""
    if value is None:
        return ""
    original = str(value).strip()
    if not original:
        return ""

    s = original
    for ch in (' ', '\u00a0', ',', '.', '_'):
        s = s.replace(ch, '')

    if not s.isdigit():
        return original

    return f"{int(s):,}".replace(',', ' ')

app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-change-me")
app.config["MAX_CONTENT_LENGTH"] = MAX_TOTAL_MB * 1024 * 1024


# ----------------------------
# Helpers
# ----------------------------

def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _new_id() -> str:
    return uuid.uuid4().hex[:10].upper()


def _original_ext(filename: str) -> str:
    """Return the original lowercase extension with leading dot, or an empty string."""
    name = Path(filename or "").name
    suffix = Path(name).suffix.lower()
    if suffix and suffix[1:] in ALLOWED_EXT:
        return suffix
    return ""


def _allowed_file(filename: str) -> bool:
    return bool(_original_ext(filename))


def _safe_upload_filename(original_filename: str) -> str:
    """Make a safe filename while preserving the original image extension.

    Werkzeug's secure_filename() can turn Cyrillic filenames like `фото.jpg`
    into `jpg` with no dot/extension. Then the file is saved successfully,
    but the public card does not recognise it as an image and shows logo.jpeg.
    This helper sanitises the stem and then deliberately re-attaches the
    original extension.
    """
    original_name = Path(original_filename or "").name
    ext = _original_ext(original_name)
    raw_stem = Path(original_name).stem
    safe_stem = secure_filename(raw_stem).strip("._-")
    if not safe_stem:
        safe_stem = f"photo_{uuid.uuid4().hex[:8]}"
    if not ext:
        # Keep a usable name even for a non-image/unknown file; current forms accept image/*,
        # but this avoids accidental empty filenames.
        safe_whole = secure_filename(original_name).strip("._-")
        return safe_whole or f"file_{uuid.uuid4().hex[:8]}"
    return f"{safe_stem}{ext}"


def _guess_image_mime(path: Path) -> str:
    """Detect common browser-displayable image types by file signature."""
    try:
        with path.open("rb") as f:
            head = f.read(64)
    except Exception:
        return ""

    if head.startswith(b"\xff\xd8\xff"):
        return "image/jpeg"
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return "image/png"
    if head.startswith((b"GIF87a", b"GIF89a")):
        return "image/gif"
    if len(head) >= 12 and head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return "image/webp"
    return ""


def _browser_image_mime_for(sid: str, filename: str) -> str:
    """Return MIME type if the file can be displayed as an <img>, otherwise ''."""
    clean = Path(filename or "").name
    ext = clean.rsplit(".", 1)[-1].lower() if "." in clean else ""
    if ext in BROWSER_IMAGE_EXT:
        return {
            "jpg": "image/jpeg",
            "jpeg": "image/jpeg",
            "png": "image/png",
            "webp": "image/webp",
            "gif": "image/gif",
        }.get(ext, "")

    # Backward compatibility for old Render uploads saved without an extension
    # because the original filename was Cyrillic.
    found = _find_upload_file(sid, clean)
    if found:
        return _guess_image_mime(found)
    return ""


def _csv_columns() -> list[str]:
    # Единый CSV для карточек (NR KITAP)
    return [
        "id",
        "created_utc",
        "kind",
        "title",
        "price_tenge",
        "phone",
        "description",
        "photos",
        "password",
    ]


def _comment_columns() -> list[str]:
    # Комментарии обычных пользователей к карточкам
    return [
        "id",
        "card_id",
        "created_utc",
        "contact",
        "message",
    ]


def _ensure_comments_csv_header() -> None:
    """Ensure comments CSV exists with the expected header."""
    if not COMMENTS_CSV.exists():
        with COMMENTS_CSV.open("w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(_comment_columns())
        return

    with COMMENTS_CSV.open("r", encoding="utf-8", newline="") as f:
        reader = csv.reader(f)
        rows = list(reader)

    if not rows:
        with COMMENTS_CSV.open("w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(_comment_columns())
        return

    expected = _comment_columns()
    if rows[0] != expected:
        # conservative migration: keep known columns and add missing ones
        old_header = rows[0]
        migrated = [expected]
        for r in rows[1:]:
            old = {old_header[i]: r[i] for i in range(min(len(old_header), len(r)))}
            migrated.append([old.get(c, "") for c in expected])
        with COMMENTS_CSV.open("w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerows(migrated)


def _read_all_comments() -> list[dict]:
    if not COMMENTS_CSV.exists():
        return []
    with COMMENTS_CSV.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows: list[dict] = []
        for r in reader:
            if not (r.get("id") or "").strip():
                continue
            rows.append({c: (r.get(c, "") or "") for c in _comment_columns()})
        return rows


def _write_all_comments(rows: list[dict]) -> None:
    tmp = COMMENTS_CSV.with_suffix(".tmp")
    cols = _comment_columns()
    with tmp.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: (r.get(c, "") or "") for c in cols})
    tmp.replace(COMMENTS_CSV)


def _agent_profile_defaults() -> dict:
    return {
        "name": "",
        "role": "",
        "bio": "",
        "photo": "",
        "threads": "",
        "instagram": "",
        "whatsapp": "",
        "telegram": "",
        "website": "",
        "extra_label": "",
        "extra_url": "",
    }


def _clean_url_value(value: str, network: str = "") -> str:
    """Normalise common social/contact values into clickable public links."""
    v = (value or "").strip()
    if not v:
        return ""

    if network in {"telegram", "instagram", "threads"}:
        username = v.strip()
        if username.startswith("@"):
            username = username[1:]
        if network == "telegram" and "/" not in username and "." not in username:
            return f"https://t.me/{username}"
        if network == "instagram" and "/" not in username and "." not in username:
            return f"https://instagram.com/{username}"
        if network == "threads" and "/" not in username and "." not in username:
            return f"https://www.threads.net/@{username}"

    if network == "whatsapp":
        raw = v.replace(" ", "").replace("-", "").replace("(", "").replace(")", "")
        if raw.startswith("+") and raw[1:].isdigit():
            return f"https://wa.me/{raw[1:]}"
        if raw.isdigit():
            return f"https://wa.me/{raw}"

    if v.startswith(("http://", "https://", "mailto:", "tel:")):
        return v
    return f"https://{v}"


def _read_agent_profile() -> dict:
    profile = _agent_profile_defaults()
    if AGENT_PROFILE_JSON.exists():
        try:
            loaded = json.loads(AGENT_PROFILE_JSON.read_text(encoding="utf-8"))
            if isinstance(loaded, dict):
                for key in profile:
                    profile[key] = str(loaded.get(key, "") or "").strip()
        except Exception:
            pass

    # Backward/Render-disk fallback: if JSON says no photo but an uploaded file exists,
    # use the first available profile image.
    photos = _image_photos(AGENT_PROFILE_SID, _list_photos(AGENT_PROFILE_SID))
    if profile.get("photo") not in photos:
        profile["photo"] = photos[0] if photos else ""

    links = []
    for key, label in [
        ("threads", "Threads"),
        ("instagram", "Instagram"),
        ("whatsapp", "WhatsApp"),
        ("telegram", "Telegram"),
        ("website", "Сайт"),
    ]:
        url = _clean_url_value(profile.get(key, ""), key)
        if url:
            links.append({"label": label, "url": url})

    extra_url = _clean_url_value(profile.get("extra_url", ""), "")
    if extra_url:
        links.append({"label": profile.get("extra_label") or "Ссылка", "url": extra_url})

    profile["links"] = links
    profile["has_content"] = bool(profile.get("name") or profile.get("role") or profile.get("bio") or profile.get("photo") or links)
    return profile


def _write_agent_profile(profile: dict) -> None:
    current = _agent_profile_defaults()
    for key in current:
        current[key] = str(profile.get(key, "") or "").strip()
    tmp = AGENT_PROFILE_JSON.with_suffix(".tmp")
    tmp.write_text(json.dumps(current, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(AGENT_PROFILE_JSON)


def _ensure_agent_offer_password_file() -> None:
    """Create the backend secret-word file for agent offers if it does not exist."""
    if not AGENT_OFFER_PASSWORD_FILE.exists():
        AGENT_OFFER_PASSWORD_FILE.write_text(DEFAULT_AGENT_OFFER_PASSWORD, encoding="utf-8")


def _read_agent_offer_password() -> str:
    """Read the secret word required to publish an agent offer.

    The public form always shows the visible default value "Free".
    If this backend file is changed later, the visible default does not change;
    only users who know the new secret word can submit an offer.
    """
    _ensure_agent_offer_password_file()
    try:
        value = AGENT_OFFER_PASSWORD_FILE.read_text(encoding="utf-8").strip()
    except Exception:
        value = ""
    return value or DEFAULT_AGENT_OFFER_PASSWORD


def _save_agent_profile_photo(file_storage) -> str:
    """Save one public profile photo and return its filename."""
    if not file_storage or not getattr(file_storage, "filename", ""):
        return ""
    if not _allowed_file(file_storage.filename):
        return ""

    profile_dir = UPLOADS_DIR / AGENT_PROFILE_SID
    profile_dir.mkdir(parents=True, exist_ok=True)

    # Keep only one active profile photo to avoid confusion.
    for old in profile_dir.iterdir():
        if old.is_file():
            old.unlink()

    safe = _safe_upload_filename(file_storage.filename)
    target = profile_dir / safe
    if target.exists():
        target = profile_dir / f"{target.stem}_{uuid.uuid4().hex[:6]}{target.suffix}"
    file_storage.save(target)
    return target.name


def _save_comment(card_id: str, contact: str, message: str) -> str:
    _ensure_comments_csv_header()
    cid = _new_id()
    with COMMENTS_CSV.open("a", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([cid, card_id, _now_iso(), contact, message])
    return cid


def _comments_by_card() -> dict[str, list[dict]]:
    out: dict[str, list[dict]] = {}
    for c in _read_all_comments():
        card_id = (c.get("card_id") or "").strip()
        if not card_id:
            continue
        out.setdefault(card_id, []).append(c)
    # newest first inside each card
    for items in out.values():
        items.sort(key=lambda x: x.get("created_utc", ""), reverse=True)
    return out


def _ensure_csv_header() -> None:
    """Ensure CSV exists with the expected header.
    If file exists but header is missing 'password', do a simple migration.
    """
    if not SUBMISSIONS_CSV.exists():
        with SUBMISSIONS_CSV.open("w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(_csv_columns())
        return

    # Migration: add missing columns to existing CSV (most importantly 'password')
    with SUBMISSIONS_CSV.open("r", encoding="utf-8", newline="") as f:
        reader = csv.reader(f)
        rows = list(reader)

    if not rows:
        with SUBMISSIONS_CSV.open("w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(_csv_columns())
        return

    header = rows[0]
    expected = _csv_columns()

    if header == expected:
        return

    if "password" not in header:
        new_header = header + ["password"]
        new_rows = [new_header]
        for r in rows[1:]:
            new_rows.append(r + [""])
        with SUBMISSIONS_CSV.open("w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerows(new_rows)
        return

    # If header differs in other ways, keep it as-is (avoid data loss).
    return


def _save_submission_row(
    sid: str,
    created_utc: str,
    kind: str,
    title: str,
    price_tenge: str,
    phone: str,
    description: str,
    photos: List[str],
    password: str = "",
):
    _ensure_csv_header()
    with SUBMISSIONS_CSV.open("a", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            sid,
            created_utc,
            kind,
            title,
            price_tenge,
            phone,
            description,
            ";".join(photos),
            password,
        ])


def _read_all_rows() -> list[dict]:
    if not SUBMISSIONS_CSV.exists():
        return []
    with SUBMISSIONS_CSV.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        rows: list[dict] = []
        for r in reader:
            if not (r.get("id") or "").strip():
                continue
            rows.append(r)
        return rows


def _write_all_rows(rows: list[dict]) -> None:
    # атомарная запись
    tmp = SUBMISSIONS_CSV.with_suffix(".tmp")
    cols = _csv_columns()
    with tmp.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            out = {c: (r.get(c, "") or "") for c in cols}
            w.writerow(out)
    tmp.replace(SUBMISSIONS_CSV)


def _find_row(rows: list[dict], sid: str) -> Optional[dict]:
    for r in rows:
        if (r.get("id") or "").strip() == sid:
            return r
    return None


def _upload_roots() -> list[Path]:
    """Possible upload roots.

    Render deployments often evolve: older versions may have saved files into
    the repository-local ./uploads folder, while production versions with a
    persistent disk usually save them into /var/data/uploads. To avoid showing
    the NR logo when files do exist, public cards and admin previews search all
    plausible upload roots, but new uploads are still saved to UPLOADS_DIR.
    """
    candidates = [
        UPLOADS_DIR,
        BASE_DIR / "uploads",
        DATA_DIR.parent / "uploads",
        DATA_DIR / "uploads",
        Path("/var/data/uploads"),
    ]

    roots: list[Path] = []
    seen: set[str] = set()
    for c in candidates:
        try:
            r = c.resolve()
        except Exception:
            continue
        key = str(r)
        if key in seen:
            continue
        roots.append(r)
        seen.add(key)
    return roots


def _list_photos(sid: str) -> list[str]:
    """List files for a card from all known upload roots, CSV-safe filenames only."""
    names: list[str] = []
    seen: set[str] = set()
    for root in _upload_roots():
        d = root / sid
        if not d.exists() or not d.is_dir():
            continue
        for p in sorted(d.iterdir(), key=lambda x: x.name.lower()):
            if not p.is_file():
                continue
            clean = Path(p.name).name
            if not clean or clean in seen:
                continue
            names.append(clean)
            seen.add(clean)
    return names


def _find_upload_file(sid: str, filename: str) -> Optional[Path]:
    """Find an uploaded file for serving, searching all known upload roots safely."""
    clean = Path(filename).name
    if not clean:
        return None
    for root in _upload_roots():
        base = (root / sid).resolve()
        p = (base / clean).resolve()
        try:
            p.relative_to(base)
        except ValueError:
            continue
        if p.exists() and p.is_file():
            return p
    return None


def _photos_from_csv_or_disk(sid: str, photos_raw: str) -> list[str]:
    """Return card files from CSV plus a disk fallback.

    Older cards may already have files in uploads/<id>/ while the CSV
    `photos` field is empty or stale. The public card gallery must still
    use those uploaded files instead of falling back to the NR logo.
    CSV order is kept first; disk-only files are appended.
    """
    from_csv = [p.strip() for p in (photos_raw or "").split(";") if p.strip()]
    from_disk = _list_photos(sid)

    merged: list[str] = []
    seen: set[str] = set()
    for name in from_csv + from_disk:
        # keep only plain filenames to avoid path traversal through CSV edits
        clean = Path(name).name
        if not clean or clean in seen:
            continue
        merged.append(clean)
        seen.add(clean)
    return merged


def _image_photos(sid: str, photos: list[str]) -> list[str]:
    """Return only files that a browser can actually render in the card gallery.

    This checks both filename extension and, for legacy extensionless uploads,
    the file signature on disk.
    """
    out: list[str] = []
    for name in photos:
        clean = Path(name or "").name
        if not clean:
            continue
        if _browser_image_mime_for(sid, clean):
            out.append(clean)
    return out


def _thumb_url(sid: str, kind: str, photos: list[str]) -> str:
    # превью: первое изображение, иначе лого
    if photos:
        first = photos[0]
        ext = first.rsplit(".", 1)[-1].lower() if "." in first else ""
        if ext in {"jpg","jpeg","png","webp","gif","heic","heif"}:
            return f"/uploads/{sid}/{quote(first)}"
    return "/static/logo.jpeg"

    # продавцы: первое фото, иначе лого
    if photos:
        return f"/uploads/{sid}/{quote(photos[0])}"
    return "/static/logo.jpeg"


def _load_submissions(limit: int = 200, highlight_id: str = "") -> list[dict]:
    """Newer-first list for public page.

    If highlight_id is provided and exists, move that card to the first position
    while keeping the rest of the list in normal newest-first order.
    """
    if not SUBMISSIONS_CSV.exists():
        return []

    comments_map = _comments_by_card()
    items: list[dict] = []
    with SUBMISSIONS_CSV.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            sid = (row.get("id") or "").strip()
            if not sid:
                continue

            kind = (row.get("kind") or "material").strip().lower()

            photos_raw = (row.get("photos") or "").strip()
            photos = _photos_from_csv_or_disk(sid, photos_raw)

            image_photos = _image_photos(sid, photos)

            items.append({
                "id": sid,
                "created_utc": (row.get("created_utc") or "").strip(),
                "kind": kind,
                "title": (row.get("title") or "").strip(),
                "price_tenge": (row.get("price_tenge") or "").strip(),
                "phone": (row.get("phone") or "").strip(),
                "description": (row.get("description") or "").strip(),
                "photos": photos,
                "image_photos": image_photos,
                "thumb_url": _thumb_url(sid, kind, image_photos),
                "password": (row.get("password") or "").strip(),
                "comments": comments_map.get(sid, []),
                "comment_count": len(comments_map.get(sid, [])),
            })

    # newest first: created_utc is ISO, so lexicographic sort works
    items.sort(key=lambda x: x.get("created_utc", ""), reverse=True)

    highlight = (highlight_id or "").strip().upper()
    if highlight:
        exact = [x for x in items if (x.get("id") or "").strip().upper() == highlight]
        rest = [x for x in items if (x.get("id") or "").strip().upper() != highlight]
        items = exact + rest

    return items[:limit]


# ----------------------------
# Public routes
# ----------------------------

@app.get("/")
def index():
    find_id = (request.args.get("find_id") or "").strip().upper()
    submissions = _load_submissions(
        limit=int(os.environ.get("MAX_LISTINGS", "200")),
        highlight_id=find_id,
    )

    unlocked = set(session.get("unlocked_cards", []) or [])
    found_id = False
    for s in submissions:
        sid = s.get("id")
        if find_id and sid and sid.upper() == find_id:
            found_id = True
            s["highlighted"] = True
        else:
            s["highlighted"] = False

        s["unlocked"] = bool(sid and sid in unlocked)

        # Если карточка защищена паролем и ещё не разблокирована —
        # показываем безопасное превью (без доступа к реальному файлу)
        if (s.get("password") or "").strip() and not s["unlocked"]:
            s["thumb_url"] = "/static/locked_thumb.svg"

    return render_template(
        "index.html",
        submissions=submissions,
        agent_profile=_read_agent_profile(),
        find_id=find_id,
        found_id=found_id,
    )


@app.post("/submit")
def submit():
    # Публичное создание заявки покупателя без загрузки файлов.
    title = (request.form.get("title") or "").strip()
    price_tenge = (request.form.get("price") or "").strip()
    phone = (request.form.get("phone") or "").strip()
    description = (request.form.get("description") or "").strip()

    if not title:
        flash("Напишите, что вы хотите купить.")
        return redirect(url_for("index") + "#buy-form")
    if not description:
        flash("Добавьте описание заявки.")
        return redirect(url_for("index") + "#buy-form")

    sid = _new_id()
    _save_submission_row(
        sid=sid,
        created_utc=_now_iso(),
        kind="buy",
        title=title[:240],
        price_tenge=price_tenge[:80],
        phone=phone[:160],
        description=description[:3000],
        photos=[],
        password="",
    )

    flash("Заявка на покупку создана.")
    return redirect(url_for("index") + f"#card-{sid}")


@app.post("/comment/<sid>")
def add_comment(sid: str):
    rows = _read_all_rows()
    if not _find_row(rows, sid):
        abort(404)

    contact = (request.form.get("contact") or "").strip()
    offer_password = (request.form.get("offer_password") or "").strip()
    message = (request.form.get("message") or "").strip()

    if not contact:
        flash("Укажите контакт агента, чтобы отправить предложение.")
        return redirect(url_for("index") + f"#card-{sid}")
    if not offer_password:
        flash("Введите секретное слово агента.")
        return redirect(url_for("index") + f"#card-{sid}")
    expected_password = _read_agent_offer_password()
    if not hmac.compare_digest(offer_password, expected_password):
        flash("Неверное секретное слово агента.")
        return redirect(url_for("index") + f"#card-{sid}")
    if not message:
        flash("Напишите текст предложения агента.")
        return redirect(url_for("index") + f"#card-{sid}")

    contact = contact[:COMMENT_CONTACT_MAX]
    message = message[:COMMENT_MESSAGE_MAX]
    _save_comment(card_id=sid, contact=contact, message=message)
    flash("Предложение агента добавлено.")
    return redirect(url_for("index") + f"#card-{sid}")


@app.get("/thanks/<sid>")
def thanks(sid: str):
    rows = _read_all_rows()
    r = _find_row(rows, sid)
    kind = ((r.get("kind") or "sell") if r else "sell").strip().lower()
    if kind not in {"buy", "sell"}:
        kind = "sell"

    photos: list[str] = []
    sub_dir = UPLOADS_DIR / sid
    if sub_dir.exists() and sub_dir.is_dir():
        photos = sorted([p.name for p in sub_dir.iterdir() if p.is_file()])

    return render_template("thanks.html", sid=sid, photos=photos, kind=kind)




@app.post("/unlock/<sid>")
def unlock(sid: str):
    password = (request.form.get("password") or "").strip()
    rows = _read_all_rows()
    r = _find_row(rows, sid)
    if not r:
        abort(404)

    expected = (r.get("password") or "").strip()
    if not expected:
        # карточка без пароля
        return redirect(url_for("index"))

    if password and hmac.compare_digest(password, expected):
        unlocked = list(session.get("unlocked_cards", []) or [])
        if sid not in unlocked:
            unlocked.append(sid)
        session["unlocked_cards"] = unlocked
        return redirect(url_for("index"))

    flash("Неверный пароль.")
    return redirect(url_for("index"))

# Inline image/file serving route used by card galleries and admin previews.
@app.get("/uploads/<sid>/<path:filename>")
def uploads(sid: str, filename: str):
    # Если на карточке стоит пароль — файлы доступны только после ввода пароля
    if not _is_admin():
        rows = _read_all_rows()
        r = _find_row(rows, sid)
        if r:
            expected = (r.get("password") or "").strip()
            if expected:
                unlocked = set(session.get("unlocked_cards", []) or [])
                if sid not in unlocked:
                    abort(403)

    found = _find_upload_file(sid, filename)
    if not found:
        abort(404)
    # inline=True: пользователь видит фото в карточке/браузере; отдельного скачивания мы не предлагаем.
    # mimetype is important for old extensionless uploads saved from Cyrillic filenames.
    mime = _browser_image_mime_for(sid, filename) or None
    return send_file(found, as_attachment=False, mimetype=mime)


@app.get("/health")
def health():
    return {"status": "ok"}


# ----------------------------
# Admin
# ----------------------------

ADMIN_KEY = (os.environ.get("ADMIN_KEY") or os.environ.get("ADMIN_PASSWORD") or "").strip()


def _is_admin() -> bool:
    if not ADMIN_KEY:
        return False
    k = session.get("admin_key", "")
    return bool(k) and hmac.compare_digest(k, ADMIN_KEY)


def admin_required(fn):
    from functools import wraps

    @wraps(fn)
    def wrapper(*args, **kwargs):
        if not _is_admin():
            return redirect(url_for("admin_login"))
        return fn(*args, **kwargs)

    return wrapper


def _admin_submissions(limit: int = 500) -> list[dict]:
    rows = _read_all_rows()
    comments_map = _comments_by_card()
    items: list[dict] = []
    for r in rows:
        sid = (r.get("id") or "").strip()
        kind = (r.get("kind") or "sell").strip().lower()
        if kind not in {"buy", "sell"}:
            kind = "sell"

        photos_raw = (r.get("photos") or "").strip()
        photos = _photos_from_csv_or_disk(sid, photos_raw)

        image_photos = _image_photos(sid, photos)

        items.append({
            "id": sid,
            "created_utc": (r.get("created_utc") or "").strip(),
            "kind": kind,
            "title": (r.get("title") or "").strip(),
            "price_tenge": (r.get("price_tenge") or "").strip(),
            "phone": (r.get("phone") or "").strip(),
            "description": (r.get("description") or "").strip(),
            "photos": photos,
            "image_photos": image_photos,
            "thumb_url": _thumb_url(sid, kind, image_photos),
            "password": (r.get("password") or "").strip(),
            "comment_count": len(comments_map.get(sid, [])),
        })

    items.sort(key=lambda x: x.get("created_utc", ""), reverse=True)
    return items[:limit]


@app.get("/admin/login")
def admin_login():
    return render_template("admin/login.html")


@app.post("/admin/login")
def admin_login_post():
    key = (request.form.get("key") or "").strip()
    if not ADMIN_KEY:
        flash("ADMIN_KEY или ADMIN_PASSWORD не задан в Render Environment.")
        return redirect(url_for("admin_login"))
    if hmac.compare_digest(key, ADMIN_KEY):
        session["admin_key"] = key
        return redirect("/admin")
    flash("Неверный ключ.")
    return redirect(url_for("admin_login"))


@app.get("/admin/logout")
def admin_logout():
    session.pop("admin_key", None)
    return redirect(url_for("index"))


@app.get("/admin")
@admin_required
def admin_index():
    subs = _admin_submissions()
    return render_template("admin/index.html", submissions=subs)





@app.get("/admin/profile")
@admin_required
def admin_profile():
    return render_template("admin/profile.html", profile=_read_agent_profile())


@app.post("/admin/profile")
@admin_required
def admin_profile_save():
    profile = _read_agent_profile()
    for key in [
        "name",
        "role",
        "bio",
        "threads",
        "instagram",
        "whatsapp",
        "telegram",
        "website",
        "extra_label",
        "extra_url",
    ]:
        profile[key] = (request.form.get(key) or "").strip()

    photo = request.files.get("photo")
    saved_photo = _save_agent_profile_photo(photo)
    if saved_photo:
        profile["photo"] = saved_photo

    _write_agent_profile(profile)
    flash("Профиль агента сохранён.")
    return redirect(url_for("admin_profile"))


@app.post("/admin/profile/photo_delete")
@admin_required
def admin_profile_photo_delete():
    profile_dir = UPLOADS_DIR / AGENT_PROFILE_SID
    if profile_dir.exists() and profile_dir.is_dir():
        for old in profile_dir.iterdir():
            if old.is_file():
                old.unlink()
    profile = _read_agent_profile()
    profile["photo"] = ""
    _write_agent_profile(profile)
    flash("Фото профиля удалено.")
    return redirect(url_for("admin_profile"))


@app.get("/admin/new")
@admin_required
def admin_new():
    return render_template("admin/new.html")


@app.post("/admin/create")
@admin_required
def admin_create():
    # Создаём новую заявку без загрузки файлов.
    title = (request.form.get("title") or "").strip()
    price_tenge = (request.form.get("price") or "").strip()
    phone = (request.form.get("phone") or "").strip()
    description = (request.form.get("description") or "").strip()

    sid = _new_id()
    created_utc = _now_iso()

    _save_submission_row(
        sid=sid,
        created_utc=created_utc,
        kind="buy",
        title=title,
        price_tenge=price_tenge,
        phone=phone,
        description=description,
        photos=[],
        password="",
    )

    flash("Заявка создана.")
    return redirect(f"/admin/edit/{sid}")


@app.get("/admin/edit/<sid>")
@admin_required
def admin_edit(sid: str):
    rows = _read_all_rows()
    r = _find_row(rows, sid)
    if not r:
        abort(404)

    photos = _list_photos(sid)
    first_photo = photos[0] if photos else ""
    row = {c: (r.get(c, "") or "") for c in _csv_columns()}
    comments = _comments_by_card().get(sid, [])
    return render_template("admin/edit.html", sid=sid, row=row, photos=photos, first_photo=first_photo, comments=comments)


@app.post("/admin/save/<sid>")
@admin_required
def admin_save(sid: str):
    rows = _read_all_rows()
    r = _find_row(rows, sid)
    if not r:
        abort(404)

    r["kind"] = "buy"
    r["title"] = (request.form.get("title") or "").strip()
    r["price_tenge"] = (request.form.get("price_tenge") or "").strip()
    r["phone"] = (request.form.get("phone") or "").strip()
    r["description"] = (request.form.get("description") or "").strip()
    r["password"] = ""
    r["photos"] = ""

    _write_all_rows(rows)
    flash("Сохранено.")
    return redirect(f"/admin/edit/{sid}")


@app.post("/admin/delete/<sid>")
@admin_required
def admin_delete(sid: str):
    rows = _read_all_rows()
    rows2 = [r for r in rows if (r.get("id") or "").strip() != sid]
    _write_all_rows(rows2)

    d = UPLOADS_DIR / sid
    if d.exists() and d.is_dir():
        shutil.rmtree(d)

    comments = [c for c in _read_all_comments() if (c.get("card_id") or "").strip() != sid]
    _write_all_comments(comments)

    flash(f"Удалено: {sid}")
    return redirect("/admin")


@app.post("/admin/photo_delete/<sid>/<path:filename>")
@admin_required
def admin_photo_delete(sid: str, filename: str):
    p = (UPLOADS_DIR / sid / filename).resolve()
    base = (UPLOADS_DIR / sid).resolve()
    if not str(p).startswith(str(base)):
        abort(400)

    if p.exists() and p.is_file():
        p.unlink()

    rows = _read_all_rows()
    r = _find_row(rows, sid)
    if r:
        r["photos"] = ";".join(_list_photos(sid))
        _write_all_rows(rows)

    return redirect(f"/admin/edit/{sid}")


@app.post("/admin/upload/<sid>")
@admin_required
def admin_upload(sid: str):
    # Загрузку файлов в карточки отключили: заявки теперь только текстовые.
    abort(404)


@app.post("/admin/comment_save/<cid>")
@admin_required
def admin_comment_save(cid: str):
    rows = _read_all_comments()
    target = None
    for c in rows:
        if (c.get("id") or "").strip() == cid:
            target = c
            break

    if not target:
        abort(404)

    contact = (request.form.get("contact") or "").strip()
    message = (request.form.get("message") or "").strip()

    if not contact:
        flash("Контакт в предложении агента не может быть пустым.")
        return redirect(f"/admin/edit/{target.get('card_id')}")
    if not message:
        flash("Текст предложения агента не может быть пустым.")
        return redirect(f"/admin/edit/{target.get('card_id')}")

    target["contact"] = contact[:COMMENT_CONTACT_MAX]
    target["message"] = message[:COMMENT_MESSAGE_MAX]
    _write_all_comments(rows)
    flash("Предложение агента сохранено.")
    return redirect(f"/admin/edit/{target.get('card_id')}")


@app.post("/admin/comment_delete/<cid>")
@admin_required
def admin_comment_delete(cid: str):
    rows = _read_all_comments()
    target = None
    rows2 = []
    for c in rows:
        if (c.get("id") or "").strip() == cid:
            target = c
            continue
        rows2.append(c)
    _write_all_comments(rows2)
    flash("Комментарий удалён.")
    if target and (target.get("card_id") or "").strip():
        return redirect(f"/admin/edit/{target.get('card_id')}")
    return redirect("/admin")


@app.get("/admin/debug/<sid>")
@admin_required
def admin_debug_card(sid: str):
    rows = _read_all_rows()
    r = _find_row(rows, sid)
    if not r:
        abort(404)

    photos_raw = (r.get("photos") or "").strip()
    photos_from_csv = [p.strip() for p in photos_raw.split(";") if p.strip()]
    root_info = []
    for root in _upload_roots():
        d = root / sid
        files = []
        if d.exists() and d.is_dir():
            files = sorted([p.name for p in d.iterdir() if p.is_file()])
        root_info.append({
            "root": str(root),
            "card_dir": str(d),
            "exists": d.exists(),
            "files": files,
        })

    return render_template(
        "admin/debug.html",
        sid=sid,
        row=r,
        photos_from_csv=photos_from_csv,
        photos_final=_photos_from_csv_or_disk(sid, photos_raw),
        image_photos=_image_photos(sid, _photos_from_csv_or_disk(sid, photos_raw)),
        root_info=root_info,
        uploads_dir=str(UPLOADS_DIR),
        data_dir=str(DATA_DIR),
        base_dir=str(BASE_DIR),
    )


@app.get("/admin/comments_csv")
@admin_required
def admin_comments_csv_download():
    _ensure_comments_csv_header()
    return send_file(COMMENTS_CSV, as_attachment=True, download_name="comments.csv")


@app.get("/admin/csv")
@admin_required
def admin_csv_download():
    if not SUBMISSIONS_CSV.exists():
        abort(404)
    return send_file(SUBMISSIONS_CSV, as_attachment=True, download_name="submissions.csv")


if __name__ == "__main__":
    port = int(os.environ.get("PORT", "10000"))
    app.run(host="0.0.0.0", port=port)