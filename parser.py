"""
Парсер электоральной статистики с сайта Избиркома (izbirkom.ru).

Собирает по каждому УИК округа: открытие помещений, явку по дням, заявления
«Мобильного избирателя» и результаты голосования. Сохраняет в CSV и (по желанию)
в Google Таблицу. Подробности — в README.md.

Запуск:
    python parser.py              # обычный запуск / продолжение после остановки
    python parser.py --reset      # начать сбор заново, удалив сохранённый прогресс
    python parser.py --wait       # ждать появления результатов на сайте (можно оставить на ночь)
"""

import argparse
import csv
import html as _html
import json
import os
import random
import re
import sys
import time
import unicodedata
from datetime import timedelta
from html.parser import HTMLParser

import undetected_chromedriver as uc

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# Личные настройки (ссылка на округ, таблица) хранятся в config.json — см. README.md
CONFIG_FILE = os.path.join(BASE_DIR, "config.json")
CREDENTIALS_FILE = os.path.join(BASE_DIR, "credentials.json")
STATE_FILE = os.path.join(BASE_DIR, "parser_state.json")
CSV_FILE = os.path.join(BASE_DIR, "results.csv")

# ==============================================================================
# РАСШИРЕННЫЕ НАСТРОЙКИ (обычно менять не нужно)
# ==============================================================================

# Отчёты уровня ТИК (УИКи идут строками). Ключ станет префиксом названий колонок.
TIK_REPORTS = {
    "Открытие": "voting-flow?type=0&report=238",
    "Явка Д1": "voting-flow?type=2&report=453",
    "Явка Д2": "voting-flow?type=4&report=453",
    "Явка Д3": "voting-flow?type=6&report=453",
}

# Отчёты уровня УИК (открываются для каждого участка отдельно)
UIK_REPORTS = {
    "Фед": "results?type=6&report=242",
    "Одн": "results?type=7&report=242",
    "Заявления (включены)": "mobile?type=10&report=469",
    "Заявления (исключены)": "mobile?type=111&report=475",
}

# Отчёт на уровне ОИК, из которого берём список ТИКов (в явке названия — ссылки)
DISCOVERY_REPORT = "voting-flow?type=2&report=453"

# Сокращения длинных заголовков: если в заголовке колонки есть фраза слева,
# колонка получит короткое имя справа. Проверяются по порядку.
SHORT_NAMES = [
    ("дистанционном электронном", "ДЭГ"),
    ("по месту нахождения", "По месту нахождения"),
]

# Колонки, которые не нужно сохранять (сравнение по началу названия).
# На уровне УИК эти поля в отчёте об открытии всегда пустые.
DROP_COLUMNS = [
    "Открытие | Количество избирательных участков",
    "Открытие | Приступили к работе",
]

WAIT_INTERVAL = 300      # режим ожидания: как часто (с) проверять, появились ли результаты
WAIT_FAIL_LIMIT = 3      # режим ожидания: сколько страниц результатов подряд должно не загрузиться,
                         # чтобы считать, что результаты пропали с сайта
GARBLED_COOLDOWN = 60    # пауза (с), если сайт начал отдавать искажённые данные
PAGE_TIMEOUT = 25        # сколько секунд ждать прогрузки таблицы за одну попытку
MAX_ATTEMPTS = 5         # сколько раз перезагружать страницу, если таблица не появилась
RETRY_PASSES = 2         # сколько раз в конце заново пройтись по пропущенным страницам
PAUSE_RANGE = (1.5, 3.0)  # случайная пауза между страницами
CSV_DELIMITER = ";"       # ";" и десятичная запятая — чтобы CSV сразу правильно открывался в русском Excel

# ==============================================================================
# СЛУЖЕБНОЕ
# ==============================================================================

# Заполняются в setup() из config.json
CONFIG = {}
ROOT = ELECTION_ID = OIK_ID = HOME_URL = None

UIK_RE = re.compile(r"УИК\s*№\s*(\d+)", re.IGNORECASE)
COMMISSION_RE = re.compile(r"/commission/([0-9a-f-]{36})")

# JS выполняется в браузере: находит самую большую таблицу на странице и отдаёт
# её шапку (с colspan/rowspan) и строки (текст ячеек + ссылки) одним вызовом.
EXTRACT_JS = r"""
const tables = Array.from(document.querySelectorAll('table:not([data-stale])'));
if (!tables.length) return null;
let best = null, bestN = -1;
for (const t of tables) {
  const n = t.querySelectorAll('tbody tr').length;
  if (n > bestN) { best = t; bestN = n; }
}
const head = best.tHead ? Array.from(best.tHead.rows).map(tr =>
  Array.from(tr.cells).map(c => ({
    text: (c.innerText || '').trim(),
    colspan: Math.max(1, c.colSpan || 1),
    rowspan: Math.max(1, c.rowSpan || 1),
  }))) : [];
const body = [];
for (const tb of best.tBodies) {
  for (const tr of tb.rows) {
    body.push(Array.from(tr.cells).map(td => {
      const a = td.querySelector('a[href]');
      return { text: (td.innerText || '').trim(), href: a ? a.href : null };
    }));
  }
}
return { head: head, body: body };
"""


def load_config():
    if not os.path.exists(CONFIG_FILE):
        sys.exit("❌ Не найден config.json. Скопируйте config.example.json в config.json "
                 "и впишите свои ссылки (см. README.md, шаг 3).")
    try:
        with open(CONFIG_FILE, encoding="utf-8") as f:
            cfg = json.load(f)
    except json.JSONDecodeError as e:
        sys.exit(f"❌ Ошибка в config.json (строка {e.lineno}): {e.msg}. "
                 "Проверьте кавычки и запятые.")
    cfg.setdefault("google_sheet_url", "")
    cfg.setdefault("tik_urls", {})
    cfg.setdefault("chrome_version", None)
    cfg.setdefault("wait_for_results", False)
    return cfg


def setup(cfg):
    global CONFIG, ROOT, ELECTION_ID, OIK_ID, HOME_URL
    CONFIG = cfg
    m = re.search(r"^(https?://[^/]+)/election/(\d+)/commission/([0-9a-f-]{36})", cfg.get("start_url", ""))
    if not m:
        sys.exit("❌ start_url в config.json имеет неверный формат. Нужна ссылка вида\n"
                 "   http://izbirkom.ru/election/<номер>/commission/<идентификатор>/")
    ROOT, ELECTION_ID, OIK_ID = m.groups()
    # Сайт Избиркома работает только по http — по https он не открывается
    ROOT = re.sub(r"^https://", "http://", ROOT)
    HOME_URL = commission_url(OIK_ID, "?tab=info")


def commission_url(cid, tail=""):
    return f"{ROOT}/election/{ELECTION_ID}/commission/{cid}/{tail}"


def commission_id(href):
    m = COMMISSION_RE.search(href or "")
    return m.group(1) if m else None


# Невидимые символы (нулевой ширины, мягкий перенос, управляющие направлением текста)
INVISIBLE = re.compile(r"[\u00ad\u200b-\u200f\u202a-\u202e\u2060-\u2064\ufeff]")
# Латинские буквы, внешне неотличимые от русских
LAT_TO_CYR = str.maketrans("aceopxyABCEHKMOPTX", "асеорхуАВСЕНКМОРТХ")


def clean(text):
    text = unicodedata.normalize("NFKC", text or "")
    return " ".join(INVISIBLE.sub("", text).split())


def normalize_label(text):
    """Подпись строки в едином виде: без невидимых символов и латинских «двойников»."""
    t = clean(text)
    if re.search(r"[А-Яа-яЁё]", t):
        t = t.translate(LAT_TO_CYR)
    return t


def to_number(text):
    """'2608' -> 2608, '44.79%' -> 44.79, '44,79' -> 44.79. Остальное — как текст."""
    t = clean(text)
    if not t:
        return ""
    s = t.replace(" ", "").replace("%", "").replace(",", ".")
    if re.fullmatch(r"-?\d+", s):
        return int(s)
    if re.fullmatch(r"-?\d+\.\d+", s):
        return float(s)
    return t


def short_name(name):
    low = name.lower()
    for phrase, short in SHORT_NAMES:
        if phrase in low:
            return short
    return name


def header_columns(head):
    """Разворачивает многоуровневую шапку (colspan/rowspan) в названия колонок.
    Для колонки берутся два нижних уровня: например, '15:00 / Число'."""
    grid = []
    for r, cells in enumerate(head):
        while len(grid) <= r:
            grid.append({})
        c = 0
        for cell in cells:
            while c in grid[r]:
                c += 1
            for i in range(cell["rowspan"]):
                while len(grid) <= r + i:
                    grid.append({})
                for j in range(cell["colspan"]):
                    grid[r + i][c + j] = cell["text"]
            c += cell["colspan"]
    ncols = max((max(g) + 1 for g in grid if g), default=0)
    names = []
    for c in range(ncols):
        parts = []
        for g in grid:
            t = clean(g.get(c, ""))
            if not t or re.fullmatch(r"[\d\s.,]*\d[\d\s.,]*%?", t) or t.upper().startswith("ВСЕГО"):
                continue
            if not parts or parts[-1] != t:
                parts.append(t)
        names.append(" / ".join(parts[-2:]))
    return names


def parse_tik_report(data, report_name):
    """Отчёт уровня ТИК -> {'УИК №101': {'id': uuid|None, 'values': {...}}}"""
    cols = header_columns(data["head"])
    out = {}
    for row in data["body"]:
        idx = next((i for i, c in enumerate(row) if UIK_RE.search(c["text"])), None)
        if idx is None:
            continue  # строка "ВСЕГО" и прочие служебные
        uik = "УИК №" + UIK_RE.search(row[idx]["text"]).group(1)
        values = {}
        if garbled_row([c["text"] for c in row]):
            continue
        for j in range(idx + 1, len(row)):
            name = cols[j] if j < len(cols) and cols[j] else f"колонка {j}"
            key = f"{report_name} | {name}"
            if any(key.startswith(d) for d in DROP_COLUMNS):
                continue
            values[key] = to_number(row[j]["text"])
        out[uik] = {"id": commission_id(row[idx]["href"]), "values": values}
    return out


# Строки протокола определяются по смыслу подписи, а не по номеру:
# номера строк сайт иногда искажает. Порядок важен («недействительных» раньше «действительных»).
PROTOCOL_ROWS = [
    (1, "внесенных в список"),
    (2, "полученных"),
    (3, "досрочно"),
    (4, "в помещении"),
    (5, "вне помещения"),
    (6, "погашенных"),
    (7, "переносных"),
    (8, "стационарных"),
    (9, "недействительных"),
    (10, "действительных"),
    (11, "утраченных"),
    (12, "не учтенных"),
]


def protocol_line(label):
    """Номер строки протокола (1–12), 0 для прочих строк «Число…», None для партии/кандидата."""
    low = label.lower().replace("ё", "е")
    if not low.startswith("число"):
        return None
    for n, phrase in PROTOCOL_ROWS:
        if phrase in low:
            return n
    return 0


def read_labeled_rows(data):
    """[(подпись, число), ...] для строк с подписью. Проценты с сайта не берутся."""
    rows = []
    for row in data["body"]:
        texts = [c["text"] for c in row]
        if not texts or garbled_row(texts):
            continue
        li = split_row(texts)
        if li is None:
            continue
        tokens = re.findall(r"\d+(?:[.,]\d+)?\s*%?", " ".join(texts[li + 1:]))
        nums = [t.strip() for t in tokens if re.fullmatch(r"\d+", t.strip())]
        if nums:
            rows.append((normalize_label(texts[li]), int(nums[0])))
    return rows


def protocol_problems(rows):
    """Проверяет контрольные соотношения протокола. Возвращает (список нарушений, строки 1–12)."""
    lines, votes = {}, []
    for label, n in rows:
        line = protocol_line(label)
        if line is None:
            votes.append(n)
        elif line:
            lines.setdefault(line, n)
    L, problems = lines, []
    if all(k in L for k in (2, 3, 4, 5, 6, 11, 12)):
        if L[2] != L[3] + L[4] + L[5] + L[6] + L[11] - L[12]:
            problems.append("2≠3+4+5+6+11−12")
    if all(k in L for k in (7, 8, 9, 10)):
        if L[7] + L[8] != L[9] + L[10]:
            problems.append("7+8≠9+10")
    if 10 in L and votes and sum(votes) != L[10]:
        problems.append("10≠сумме голосов")
    return problems, lines


def results_valid(data):
    """Для страниц результатов: контрольные соотношения сходятся. Прочие страницы — всегда да."""
    rows = read_labeled_rows(data)
    return not rows or not protocol_problems(rows)[0]


def parse_uik_report(data, prefix):
    """Отчёт уровня УИК -> {'Фед | Число избирателей...': 419, ...}

    Страница результатов (строки с подписями): колонки называются по подписи строки
    без номера, строки без подписи игнорируются. Проценты за партии и кандидатов
    считаются здесь, как у ЦИК: от числа принявших участие в голосовании
    (бюллетени в переносных + стационарных ящиках). Добавляется колонка
    «Контроль протокола» с результатом проверки контрольных соотношений.

    Страница без подписей (заявления): значения по колонкам шапки."""
    values = {}
    rows = read_labeled_rows(data)
    if rows:
        problems, lines = protocol_problems(rows)
        total = lines.get(7, 0) + lines.get(8, 0) if 7 in lines and 8 in lines else 0
        for label, n in rows:
            key = f"{prefix} | {label}"
            values[key] = n
            if total and protocol_line(label) is None:
                values[key + " (%)"] = round(n / total * 100, 2)
        values[f"{prefix} | Контроль протокола"] = (
            "OK" if not problems else "не сходится: " + ", ".join(problems))
        return values

    cols = header_columns(data["head"])
    for row in data["body"]:
        texts = [c["text"] for c in row]
        if not texts or garbled_row(texts):
            continue
        for j, t in enumerate(texts):
            if len(texts) == 1:
                key = prefix
            else:
                name = short_name(cols[j]) if j < len(cols) and cols[j] else f"колонка {j + 1}"
                key = f"{prefix} | {name}"
            values[key] = to_number(t)
    return values


# ------------------------------------------------------------------------------
# Расшифровка отчётов Избиркома.
#
# Сервер отдаёт таблицу результатов в перемешанном виде (JSON: html + script).
# script — набор операций, которые браузер применяет к таблице, чтобы получить
# правильные числа. Названия функций и классов случайные и меняются при каждом
# запросе, поэтому операции распознаются по содержимому функций.
# ------------------------------------------------------------------------------

class DecodeError(Exception):
    pass


VOID_TAGS = {"br", "img", "hr", "input", "meta", "link", "col", "wbr", "source"}


class _Node:
    __slots__ = ("tag", "attrs", "children", "parent")

    def __init__(self, tag, attrs=None, parent=None):
        self.tag, self.attrs, self.children, self.parent = tag, dict(attrs or {}), [], parent

    def classes(self):
        return (self.attrs.get("class") or "").split()

    def elements(self):
        return [c for c in self.children if isinstance(c, _Node)]

    def iter(self):
        for c in self.children:
            if isinstance(c, _Node):
                yield c
                yield from c.iter()

    def inner(self):
        out = []
        for c in self.children:
            if isinstance(c, _Node):
                attrs = "".join(f' {k}="{_html.escape(v or "", quote=True)}"' for k, v in c.attrs.items())
                out.append(f"<{c.tag}{attrs}>{c.inner()}</{c.tag}>")
            else:
                out.append(_html.escape(c, quote=False))
        return "".join(out)

    def set_inner(self, markup):
        frag = _parse(markup)
        self.children = frag.children
        for c in self.children:
            if isinstance(c, _Node):
                c.parent = self

    def text(self):
        return "".join(c.text() if isinstance(c, _Node) else c for c in self.children)


class _TreeBuilder(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = _Node("#root")
        self.cur = self.root

    def handle_starttag(self, tag, attrs):
        node = _Node(tag, attrs, self.cur)
        self.cur.children.append(node)
        if tag not in VOID_TAGS:
            self.cur = node

    def handle_startendtag(self, tag, attrs):
        self.cur.children.append(_Node(tag, attrs, self.cur))

    def handle_endtag(self, tag):
        n = self.cur
        while n is not self.root and n.tag != tag:
            n = n.parent
        if n is not self.root:
            self.cur = n.parent

    def handle_data(self, data):
        self.cur.children.append(data)


def _parse(markup):
    b = _TreeBuilder()
    b.feed(markup)
    b.close()
    return b.root


def _lec(node):
    """Как функция lec на сайте: самый глубокий «последний дочерний элемент»."""
    els = node.elements()
    if not els:
        return node
    last = els[-1]
    if last.elements():
        return _lec(last)
    return last


def _splice(lst, start, delete, *items):
    """Array.prototype.splice из JavaScript."""
    n = len(lst)
    start = max(n + start, 0) if start < 0 else min(start, n)
    lst[start:start + delete] = list(items)


def _split_args(s):
    args, cur, quote = [], "", None
    for ch in s:
        if quote:
            cur += ch
            if ch == quote:
                quote = None
        elif ch in "'\"":
            quote = ch
            cur += ch
        elif ch == ",":
            args.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        args.append(cur.strip())
    out = []
    for a in args:
        if len(a) >= 2 and a[0] == a[-1] and a[0] in "'\"":
            out.append(a[1:-1])
        elif a == "false":
            out.append(False)
        elif a == "true":
            out.append(True)
        elif re.fullmatch(r"-?\d+", a):
            out.append(int(a))
        else:
            out.append(None)  # ссылка на таблицу
    return out


def _classify(body):
    if "getBoundingClientRect" in body:
        return "overlay"
    if "charAt" in body:
        return "insert"
    if "splice" in body and "getElementsByClassName" in body:
        return "remove"
    if "getElementsByTagName" in body and "lec(" in body:
        return "swap"
    if "getElementsByClassName" in body and "innerHTML" in body:
        return "set"
    return None


def parse_script(script):
    """Скрипт сайта -> список операций [(вид, аргументы), ...] в порядке выполнения."""
    defs = list(re.finditer(r"var\s+(\w+)\s*=\s*function\s*\(([^)]*)\)\s*\{", script))
    main_m = re.search(r"listen\(\s*document\s*,\s*['\"]DOMContentLoaded['\"]\s*,\s*(\w+)\s*\)", script)
    if not main_m:
        raise DecodeError("не найдена главная функция")
    main = main_m.group(1)

    kinds, unknown, main_body = {}, set(), None
    for i, m in enumerate(defs):
        name = m.group(1)
        end = defs[i + 1].start() if i + 1 < len(defs) else len(script)
        body = script[m.end():end]
        if name == main:
            main_body = body
        elif name == "lec":
            continue
        else:
            kind = _classify(body)
            if kind:
                kinds[name] = kind
            else:
                unknown.add(name)
    if main_body is None:
        raise DecodeError("не найдено тело главной функции")
    # Повторные наложения при изменении размера окна не нужны
    main_body = re.split(r"listen\(\s*window", main_body)[0]

    ops = []
    for m in re.finditer(r"(\w+)\(([^()]*)\)", main_body):
        name = m.group(1)
        if name in unknown:
            raise DecodeError(f"неизвестная операция {name}")
        if name in kinds:
            ops.append((kinds[name], _split_args(m.group(2))))
    return ops


def decode_report(payload):
    """JSON-ответ сервера (dict с ключами html и script) -> строки таблицы
    в том же формате, что возвращает EXTRACT_JS: {"head": [], "body": [[{"text", "href"}]]}."""
    if not isinstance(payload, dict) or not payload.get("html"):
        raise DecodeError("в ответе нет таблицы")
    root = _parse(payload["html"])
    all_nodes = list(root.iter())
    tds = [n for n in all_nodes if n.tag == "td"]

    def by_class(cls):
        return [n for n in root.iter() if cls in n.classes()]

    def td(i):
        i = int(i)
        if not 0 <= i < len(tds):
            raise DecodeError(f"нет ячейки №{i}")
        return tds[i]

    overlays = []
    for kind, a in parse_script(payload.get("script") or ""):
        if kind == "overlay":           # (класс, №ячейки)
            cls, i = a[0], a[1]
            src = by_class(cls)
            if not src:
                continue
            if "fix-col" in td(i).classes():
                td(i).set_inner(src[0].inner())
            else:
                overlays.append((i, cls))  # на экране поверх ячейки — итоговое значение блока
        elif kind == "set":             # (класс, значение)
            for n in by_class(a[0]):
                n.set_inner(str(a[1]))
        elif kind == "remove":          # (класс, позиция символа)
            for n in by_class(a[0]):
                v = list(n.inner())
                _splice(v, a[1], 1)
                n.set_inner("".join(v))
        elif kind == "swap":            # (№ячейки, №ячейки)
            x, y = _lec(td(a[0])), _lec(td(a[1]))
            xi, yi = x.inner(), y.inner()
            x.set_inner(yi)
            y.set_inner(xi)
        elif kind == "insert":          # (позиция символа, откуда, куда вставить, в какую ячейку, позиция точки)
            char_i, src_i, pos, dst_i, dot = a[:5]
            src, dst = _lec(td(src_i)), _lec(td(dst_i))
            v = list(dst.inner())
            if dot is not False:
                _splice(v, dot, 0, ".")
            s = src.inner().strip()
            ch = s[char_i] if 0 <= char_i < len(s) else ""
            _splice(v, pos, 0, ch)
            dst.set_inner("".join(v))
    # Наложенные блоки видны поверх ячеек — подставляем их итоговое содержимое
    for i, cls in overlays:
        src = by_class(cls)
        if src:
            td(i).set_inner(src[0].inner())

    # Собираем строки таблицы (только внутри tbody; невидимая строка с блоками — вне его)
    body = []
    for tbody in (n for n in all_nodes if n.tag == "tbody"):
        for tr in (n for n in tbody.iter() if n.tag == "tr"):
            cells = tr.elements()
            if not cells or any(c.tag == "th" for c in cells):
                continue  # строки-заголовки
            body.append([{"text": " ".join(c.text().split()), "href": None} for c in cells if c.tag == "td"])
    return {"head": [], "body": body}


# --- Готовность страницы -------------------------------------------------------

def has_uik_rows(data):
    rows = [[c["text"] for c in r] for r in data["body"]
            if any(UIK_RE.search(c["text"]) for c in r)]
    return bool(rows) and not any(garbled_row(t) for t in rows)


def has_commission_links(data):
    return any(commission_id(c["href"]) for row in data["body"] for c in row)


def split_row(texts):
    """Индекс ячейки-подписи (где больше всего букв) или None, если подписи нет."""
    letters = [len(re.findall(r"[A-Za-zА-Яа-яЁё]", t)) for t in texts]
    li = max(range(len(texts)), key=lambda i: letters[i])
    return li if letters[li] else None


NUM_CELL = re.compile(r"(?:\d+(?:[.,]\d+)?\s*%?\s*)*")
MIXED = re.compile(r"[A-Za-zА-Яа-яЁё]\d|\d[A-Za-zА-Яа-яЁё]")


def garbled_row(texts):
    """True, если строка выглядит искажённой защитой сайта: буквы вперемешку с цифрами
    в подписи или посторонние символы в ячейках, где должны быть только числа."""
    if not texts:
        return False
    li = split_row(texts)
    if li is not None and MIXED.search(texts[li]):
        return True
    start = li + 1 if li is not None else 0
    return any(not NUM_CELL.fullmatch(clean(t)) for t in texts[start:])


def looks_garbled(data):
    return bool(data) and any(garbled_row([c["text"] for c in r]) for r in data["body"])


def uik_ready(data):
    """Таблица УИК готова, когда во всех нумерованных строках появились значения.
    Номер строки сам по себе не считается: сайт сначала рисует каркас таблицы
    с номерами и подписями, а числа подставляет позже."""
    rows = [[c["text"] for c in r] for r in data["body"] if r]
    if not rows or any(garbled_row(t) for t in rows):
        return False
    labeled = any(split_row(t) is not None for t in rows)
    for texts in rows:
        li = split_row(texts)
        if li is None:
            if labeled:
                continue  # на странице результатов строки без подписи не нужны
            if not any(re.search(r"\d", t) for t in texts):
                return False
            continue
        numbered = li > 0 and re.fullmatch(r"\d+[а-яa-z]?", clean(texts[0]))
        if numbered and not re.search(r"\d", " ".join(texts[li + 1:])):
            return False
    return True


# --- Браузер ---------------------------------------------------------------------

def init_driver():
    options = uc.ChromeOptions()
    options.add_argument("--window-size=1920,1080")
    # Окно браузера должно быть видимым: невидимый (headless) режим сайт блокирует,
    # а капчу нужно решать вручную.
    try:
        return uc.Chrome(options=options, version_main=CONFIG.get("chrome_version"))
    except Exception as e:
        sys.exit(f"❌ Не удалось запустить Chrome: {e}\n"
                 "   Если ошибка про версию ChromeDriver — укажите chrome_version в config.json "
                 "(см. README.md, раздел «Частые проблемы»).")


# Помечает текущие таблицы как «старые», чтобы после перехода не прочитать их по ошибке
MARK_STALE_JS = "document.querySelectorAll('table').forEach(t => t.setAttribute('data-stale', '1'));"

# Переход внутри приложения через его роутер (как при клике по ссылке), без перезагрузки
NAVIGATE_JS = r"""
const u = new URL(arguments[0], location.href);
const path = u.pathname + u.search;
const el = document.querySelector('#q-app');
const app = el && el.__vue_app__;
const router = app && app.config.globalProperties.$router;
if (router) { router.push(path).catch(() => {}); return 'router'; }
history.pushState({}, '', path);
window.dispatchEvent(new PopStateEvent('popstate', { state: history.state }));
return 'popstate';
"""

# Перехват ответов сервера с отчётами (до того, как сайт перемешает таблицу на экране).
# Устанавливается один раз на загрузку страницы; при каждом вызове очищает список ответов.
HOOK_JS = r"""
if (!window.__izbHooked) {
  window.__izbHooked = true;
  const store = (url, text) => { try { (window.__izbReports = window.__izbReports || []).push({url: url, text: text}); } catch (e) {} };
  const open = XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open = function (m, u) { this.__izbUrl = String(u); return open.apply(this, arguments); };
  const send = XMLHttpRequest.prototype.send;
  XMLHttpRequest.prototype.send = function () {
    if (this.__izbUrl && this.__izbUrl.indexOf('/reports/') !== -1) {
      this.addEventListener('load', () => {
        let t;
        try { t = this.responseText; } catch (e) { t = typeof this.response === 'string' ? this.response : JSON.stringify(this.response); }
        store(this.__izbUrl, t);
      });
    }
    return send.apply(this, arguments);
  };
  if (window.fetch) {
    const f = window.fetch;
    window.fetch = function (input) {
      const u = String((input && input.url) || input);
      const p = f.apply(this, arguments);
      if (u.indexOf('/reports/') !== -1) p.then(r => r.clone().text().then(t => store(u, t))).catch(() => {});
      return p;
    };
  }
}
window.__izbReports = [];
"""

APP_READY_JS = r"""
const el = document.querySelector('#q-app');
return !!(el && el.__vue_app__) && document.body.innerText.includes('Дата голосования');
"""


def check_captcha(driver):
    """Возвращает True, если пришлось решать капчу."""
    try:
        suspicious = "captcha" in driver.current_url.lower() or "капч" in driver.page_source.lower()
    except Exception:
        return False
    if suspicious:
        print("🚨 СРАБОТАЛА ЗАЩИТА (КАПЧА)! Решите её вручную в окне браузера.")
        input("👉 После этого нажмите Enter здесь...")
        return True
    return False


def js(driver, code, *args):
    try:
        return driver.execute_script(code, *args)
    except Exception:
        return None


def wait_until(check, timeout):
    deadline = time.time() + timeout
    while time.time() < deadline:
        if check():
            return True
        time.sleep(0.7)
    return False


def same_page(driver, url):
    cur = js(driver, "return location.pathname + location.search") or ""
    target = re.sub(r"^https?://[^/]+", "", url)
    return cur == target


def warm_up(driver):
    """«Вернуться в начало»: полностью загружает главную страницу выборов."""
    for attempt in range(1, MAX_ATTEMPTS + 1):
        driver.get(HOME_URL)
        if check_captcha(driver):
            driver.get(HOME_URL)
        if wait_until(lambda: js(driver, APP_READY_JS), PAGE_TIMEOUT):
            time.sleep(1)
            return True
        wait = min(10 * attempt, 60)
        print(f"    ⚠ Главная страница не загрузилась (попытка {attempt}/{MAX_ATTEMPTS}), жду {wait} с")
        time.sleep(wait)
    return False


def spa_go(driver, url):
    """Переходит на url внутри приложения и ждёт, пока старые таблицы исчезнут со страницы."""
    if same_page(driver, url):
        return
    js(driver, HOOK_JS)
    js(driver, MARK_STALE_JS)
    js(driver, NAVIGATE_JS, url)
    wait_until(lambda: same_page(driver, url), 10)


def wait_table(driver, ready, validate=None):
    """Ждёт новую таблицу, которая удовлетворяет ready и перестала меняться.
    Возвращает (данные, None) при успехе или (None, данные), если таблица загрузилась,
    но не прошла проверку validate."""
    deadline = time.time() + PAGE_TIMEOUT
    last, stable, failed = None, 0, None
    while time.time() < deadline:
        time.sleep(0.7)
        data = js(driver, EXTRACT_JS)
        if not data or not ready(data):
            last, stable = None, 0
            continue
        # Таблица считается готовой, только когда её содержимое (не только число строк)
        # не менялось несколько проверок подряд
        snapshot = json.dumps(data, ensure_ascii=False, sort_keys=True)
        stable = stable + 1 if snapshot == last else 0
        last = snapshot
        if stable >= 2:
            if validate is None or validate(data):
                return data, None
            failed = data  # продолжаем ждать: вдруг значения ещё обновятся
    return None, failed


REPORTS_JS = "return window.__izbReports || [];"
_warned = set()


def wait_report(driver, cid, ready, validate=None):
    """Ждёт перехваченный ответ сервера с отчётом по комиссии cid и расшифровывает его.
    Возвращает (данные, None) при успехе или (None, данные), если они не прошли validate."""
    deadline = time.time() + PAGE_TIMEOUT
    failed = None
    while time.time() < deadline:
        time.sleep(0.7)
        found = [r for r in (js(driver, REPORTS_JS) or []) if cid in (r.get("url") or "")]
        if not found:
            continue
        try:
            data = decode_report(json.loads(found[-1]["text"]))
        except (ValueError, TypeError):
            continue  # ответ ещё не пришёл целиком или это не JSON
        except DecodeError as e:
            if str(e) not in _warned:
                _warned.add(str(e))
                print(f"    ⚠ Не удалось расшифровать ответ сервера: {e}. "
                      f"Возможно, сайт изменил защиту — сообщите об этом.")
            return None, None
        if not ready(data):
            continue
        if validate is None or validate(data):
            return data, None
        failed = data
        break  # расшифровка точная: ждать изменений бессмысленно
    return None, failed


def load_table(driver, url, ready, validate=None, report_cid=None):
    """Открывает отчёт так же, как человек: из загруженного приложения, переходом по ссылке.
    report_cid: если задан, данные берутся не с экрана, а из перехваченного ответа сервера
    (для результатов, которые сайт перемешивает на экране).
    Если не вышло, возвращается на главную (полная загрузка) и пробует снова.

    Если таблица не проходит validate, страница перезагружается: искажения от защиты
    сайта случайны. Если две загрузки подряд дали одинаковые данные — значит, так
    на самом деле, и они принимаются как есть."""
    prev_failed = None
    for attempt in range(1, MAX_ATTEMPTS + 1):
        app_loaded = js(driver, "return !!(document.querySelector('#q-app') || {}).__vue_app__")
        if attempt > 1 or not app_loaded:
            if not warm_up(driver):
                continue
        # Сначала на главную внутри приложения (чтобы старый отчёт гарантированно закрылся),
        # затем на нужный отчёт.
        if not same_page(driver, HOME_URL):
            spa_go(driver, HOME_URL)
            wait_until(lambda: js(driver, APP_READY_JS), PAGE_TIMEOUT)
        spa_go(driver, url)
        if report_cid:
            data, failed = wait_report(driver, report_cid, ready, validate)
        else:
            data, failed = wait_table(driver, ready, validate)
        if data:
            return data
        if failed:
            snap = json.dumps(failed, ensure_ascii=False, sort_keys=True)
            if snap == prev_failed:
                print("    ⚠ Контрольные соотношения не сходятся, но две загрузки совпали — "
                      "сохраняю как есть (см. колонку «Контроль протокола»)")
                return failed
            prev_failed = snap
            print(f"    🛡 Контрольные соотношения протокола не сходятся — похоже на искажение, "
                  f"перезагружаю (попытка {attempt}/{MAX_ATTEMPTS})")
            time.sleep(min(5 * attempt, 30))
            continue
        if check_captcha(driver):
            continue
        if not report_cid and looks_garbled(js(driver, EXTRACT_JS)):
            print(f"    🛡 Сайт отдаёт искажённые данные (похоже на защиту от ботов). "
                  f"Пауза {GARBLED_COOLDOWN} с, затем повтор.")
            time.sleep(GARBLED_COOLDOWN)
            continue
        wait = min(5 * attempt, 30)
        print(f"    ⚠ Таблица не загрузилась (попытка {attempt}/{MAX_ATTEMPTS}), "
              f"возвращаюсь в начало через {wait} с: {url}")
        time.sleep(wait)
    return None


def pause():
    time.sleep(random.uniform(*PAUSE_RANGE))


# --- Состояние и Google Таблица -------------------------------------------------

def load_state():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE, encoding="utf-8") as f:
            state = json.load(f)
        if state.get("start_url") and commission_id(state["start_url"]) != OIK_ID:
            sys.exit("❌ Сохранённый прогресс относится к другому округу (start_url изменился).\n"
                     "   Запустите с флагом --reset, чтобы начать сбор заново.")
        state["start_url"] = CONFIG["start_url"]
        return state
    return {"start_url": CONFIG["start_url"], "tiks": {}, "uiks": {}, "columns": [], "done": []}


def save_state(state):
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=1)
    os.replace(tmp, STATE_FILE)  # атомарно: файл не побьётся при сбое во время записи


def add_values(state, row, values):
    for k, v in values.items():
        if k not in state["columns"]:
            state["columns"].append(k)
        row[k] = v


def uik_number(name):
    m = UIK_RE.search(name or "")
    return int(m.group(1)) if m else 0


FIXED_COLUMNS = ["ТИК", "УИК", "Ссылка на УИК"]


def table_rows(state):
    cols = FIXED_COLUMNS + state["columns"]
    rows = [cols]
    for r in sorted(state["uiks"].values(), key=lambda r: (r["ТИК"], uik_number(r["УИК"]))):
        rows.append([r.get(c, "") for c in cols])
    return rows


def write_csv(rows):
    def fmt(v):
        if isinstance(v, float) and CSV_DELIMITER == ";":
            return str(v).replace(".", ",")
        return v
    tmp = CSV_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8-sig", newline="") as f:
        csv.writer(f, delimiter=CSV_DELIMITER).writerows([[fmt(v) for v in r] for r in rows])
    try:
        os.replace(tmp, CSV_FILE)
    except PermissionError:
        print("  ⚠ Не удалось обновить results.csv — закройте его в Excel, данные запишутся в следующий раз.")


def connect_sheet():
    url = CONFIG["google_sheet_url"]
    if not url:
        print("Google Таблица не указана — результаты будут только в results.csv")
        return None
    if not os.path.exists(CREDENTIALS_FILE):
        sys.exit("❌ Не найден credentials.json (ключ Google). См. README.md, шаг 4, "
                 "или оставьте google_sheet_url пустым, чтобы сохранять только в CSV.")
    # Принимаем полную ссылку или просто ID таблицы
    m = re.search(r"/spreadsheets/d/([a-zA-Z0-9_-]+)", url)
    if m:
        key = m.group(1)
    elif re.fullmatch(r"[a-zA-Z0-9_-]{25,}", url.strip()):
        key = url.strip()
    else:
        sys.exit("❌ google_sheet_url в config.json не похож на ссылку на Google Таблицу:\n"
                 f"   {url}\n"
                 "   Нужна ссылка вида https://docs.google.com/spreadsheets/d/<ID>/edit —\n"
                 "   откройте таблицу в браузере и скопируйте адрес из адресной строки.")
    import gspread
    print("Подключение к Google Таблице...")
    try:
        return gspread.service_account(filename=CREDENTIALS_FILE).open_by_key(key).sheet1
    except gspread.exceptions.SpreadsheetNotFound:
        sys.exit("❌ Таблица не найдена. Проверьте ссылку и что сервисному аккаунту "
                 "выдан доступ «Редактор» (README.md, шаг 4).")
    except gspread.exceptions.APIError as e:
        text = str(e)
        if "not supported for this document" in text:
            sys.exit("❌ Это файл Excel (.xlsx), загруженный на Диск, а не Google Таблица.\n"
                     "   Создайте новую Google Таблицу (или Файл → Сохранить как Google Таблицу).")
        if "403" in text or "PERMISSION_DENIED" in text:
            sys.exit("❌ Нет доступа к таблице. Добавьте email сервисного аккаунта "
                     "(…iam.gserviceaccount.com) в доступ к таблице с правами «Редактор»,\n"
                     "   и проверьте, что в Google Cloud включены Google Sheets API и Google Drive API.")
        raise


def save_outputs(sheet, state):
    rows = table_rows(state)
    write_csv(rows)
    msg = f"  💾 Сохранено: {len(rows) - 1} УИК, {len(rows[0])} колонок (results.csv"
    if sheet is not None:
        try:
            sheet.clear()
            sheet.resize(rows=max(len(rows), 2), cols=max(len(rows[0]), 1))
            sheet.update(range_name="A1", values=rows, value_input_option="RAW")
            msg += " + Google Таблица"
        except Exception as e:
            print(f"  ⚠ Не удалось обновить Google Таблицу: {e}")
    print(msg + ")")


def requeue_gaps(state, done):
    """Находит УИКи, у которых в отчёте не хватает значений, которые есть у других УИКов,
    и помечает эти страницы для повторной загрузки."""
    n = 0
    for row in state["uiks"].values():
        if not row.get("_id"):
            continue
        for prefix in UIK_REPORTS:
            task = f"res:{row['_id']}:{prefix}"
            if task not in done:
                continue
            cols = [c for c in state["columns"] if c == prefix or c.startswith(prefix + " | ")]
            if any(row.get(c, "") == "" for c in cols):
                done.discard(task)
                n += 1
    if n:
        state["done"] = sorted(done)
        print(f"🔎 Найдено страниц с пропущенными значениями: {n} — они будут загружены заново")
    return n


# --- Основная логика ---------------------------------------------------------------

def discover_tiks(driver):
    if CONFIG["tik_urls"]:
        tiks = {commission_id(u): name for name, u in CONFIG["tik_urls"].items() if commission_id(u)}
        print(f"ТИКи взяты из настроек: {len(tiks)}")
        return tiks
    print("Ищу список ТИКов на странице округа...")
    data = load_table(driver, commission_url(OIK_ID, DISCOVERY_REPORT), has_commission_links)
    tiks = {}
    for row in (data or {}).get("body", []):
        for c in row:
            cid = commission_id(c["href"])
            if cid and cid != OIK_ID:
                tiks[cid] = clean(c["text"])
                break
    if not tiks:
        sys.exit("❌ Не удалось найти ТИКи автоматически. Проверьте, что на сайте опубликованы данные,\n"
                 "   или заполните tik_urls в config.json вручную (README.md, «Частые проблемы»).")
    print(f"Найдено ТИКов: {len(tiks)}")
    return tiks


def process_tik(driver, state, done, tik_id, tik_name):
    # 1. Отчёты уровня ТИК: одна страница = все УИКи
    for rep_name, tail in TIK_REPORTS.items():
        task = f"tik:{tik_id}:{rep_name}"
        if task in done:
            continue
        print(f"  • {rep_name}")
        data = load_table(driver, commission_url(tik_id, tail), has_uik_rows)
        if not data:
            print("    ⚠ Пропущено (будет повторено при следующем запуске)")
            continue
        parsed = parse_tik_report(data, rep_name)
        for uik, info in parsed.items():
            key = f"{tik_id}|{uik}"
            row = state["uiks"].setdefault(key, {"ТИК": tik_name, "УИК": uik, "Ссылка на УИК": ""})
            if info["id"]:
                row["_id"] = info["id"]
                row["Ссылка на УИК"] = commission_url(info["id"])
            add_values(state, row, info["values"])
        print(f"    УИКов в отчёте: {len(parsed)}")
        done.add(task)
        state["done"] = sorted(done)
        save_state(state)
        pause()

    # 2. Отчёты по каждому УИКу (результаты и заявления)
    keys = sorted((k for k in state["uiks"] if k.startswith(tik_id + "|")),
                  key=lambda k: uik_number(k))
    for i, key in enumerate(keys, 1):
        row = state["uiks"][key]
        if not row.get("_id"):
            print(f"  ⚠ {row['УИК']}: нет ссылки на страницу УИК, результаты пропущены")
            continue
        for prefix, tail in UIK_REPORTS.items():
            task = f"res:{row['_id']}:{prefix}"
            if task in done:
                continue
            print(f"  [{i}/{len(keys)}] {row['УИК']} — {prefix}")
            data = load_table(driver, commission_url(row["_id"], tail), uik_ready, results_valid,
                              report_cid=row["_id"] if tail.startswith("results") else None)
            if not data:
                print("    ⚠ Пропущено (будет повторено позже)")
                RUN["fails"] += 1
                if RUN["wait"] and RUN["fails"] >= WAIT_FAIL_LIMIT:
                    raise ResultsUnavailable()
                continue
            RUN["fails"] = 0
            values = parse_uik_report(data, prefix)
            add_values(state, row, values)
            print(f"    Показателей: {len(values)}")
            done.add(task)
            state["done"] = sorted(done)
            save_state(state)
            pause()


class ResultsUnavailable(Exception):
    """Результаты перестали загружаться — похоже, их убрали с сайта."""


RUN = {"wait": False, "fails": 0}


def count_remaining(state, done):
    n = 0
    for tik_id in state["tiks"]:
        n += sum(f"tik:{tik_id}:{r}" not in done for r in TIK_REPORTS)
    for row in state["uiks"].values():
        if row.get("_id"):
            n += sum(f"res:{row['_id']}:{p}" not in done for p in UIK_REPORTS)
    return n


def results_available(driver, state, done):
    """Одна быстрая проверка: открывается ли страница результатов хотя бы одного УИКа."""
    rows = [r for r in state["uiks"].values() if r.get("_id")]
    if not rows:
        return True  # УИКи ещё не известны — проверять нечего
    prefix, tail = next(iter(UIK_REPORTS.items()))
    # Предпочитаем УИК, чьи результаты уже когда-то загружались: его страница точно рабочая
    row = next((r for r in rows if f"res:{r['_id']}:{prefix}" in done), rows[0])
    try:
        driver.get(HOME_URL)
        if not wait_until(lambda: js(driver, APP_READY_JS), PAGE_TIMEOUT):
            return False
        spa_go(driver, commission_url(row["_id"], tail))
        data, failed = wait_report(driver, row["_id"], uik_ready)
        return bool(data or failed)
    except Exception:
        return False


def wait_for_results(driver, state, done):
    checks = 0
    while not results_available(driver, state, done):
        checks += 1
        print(f"[{time.strftime('%d.%m %H:%M')}] 💤 Результатов на сайте пока нет "
              f"(проверка №{checks}). Следующая через {WAIT_INTERVAL // 60} мин...")
        time.sleep(WAIT_INTERVAL)
    if checks:
        print(f"[{time.strftime('%d.%m %H:%M')}] ✅ Результаты появились — продолжаю сбор")


def run_pass(driver, sheet, state, done):
    """Полный проход по всем ТИКам и повторные проходы по пропущенным страницам."""
    tiks = list(state["tiks"].items())
    start = time.time()
    for n, (tik_id, tik_name) in enumerate(tiks, 1):
        print(f"\n=== ТИК {n}/{len(tiks)}: {tik_name} ===")
        process_tik(driver, state, done, tik_id, tik_name)
        save_outputs(sheet, state)
        eta = (time.time() - start) / n * (len(tiks) - n)
        print(f"  ⏱ Осталось примерно: {timedelta(seconds=int(eta))}")

    for p in range(1, RETRY_PASSES + 1):
        requeue_gaps(state, done)
        if not count_remaining(state, done):
            break
        before = len(done)
        print(f"\n=== Повторный проход {p}/{RETRY_PASSES} по пропущенным страницам ===")
        for tik_id, tik_name in tiks:
            process_tik(driver, state, done, tik_id, tik_name)
        save_outputs(sheet, state)
        if len(done) == before:
            break  # за проход ничего нового не загрузилось


def main():
    ap = argparse.ArgumentParser(description="Парсер данных Избиркома (см. README.md)")
    ap.add_argument("--reset", action="store_true",
                    help="удалить сохранённый прогресс и начать сбор заново")
    ap.add_argument("--wait", action="store_true",
                    help="ждать, пока результаты появятся на сайте, и собирать их по мере появления")
    args = ap.parse_args()

    setup(load_config())
    RUN["wait"] = args.wait or bool(CONFIG["wait_for_results"])
    if args.reset and os.path.exists(STATE_FILE):
        os.remove(STATE_FILE)
        print("Сохранённый прогресс удалён, начинаем заново.")
    if RUN["wait"]:
        print(f"Режим ожидания включён: если результатов нет, проверяю сайт раз в "
              f"{WAIT_INTERVAL // 60} мин. Остановить — Ctrl+C.")

    state = load_state()
    done = set(state["done"])
    requeue_gaps(state, done)
    sheet = connect_sheet()
    driver = init_driver()
    try:
        # Список ТИКов
        while not state["tiks"]:
            try:
                state["tiks"] = discover_tiks(driver)
                save_state(state)
            except SystemExit:
                if not RUN["wait"]:
                    raise
                print(f"[{time.strftime('%d.%m %H:%M')}] 💤 Сайт пока не отдаёт список ТИКов, "
                      f"повтор через {WAIT_INTERVAL // 60} мин...")
                time.sleep(WAIT_INTERVAL)

        last_remaining = None
        while True:
            try:
                if RUN["wait"]:
                    wait_for_results(driver, state, done)
                run_pass(driver, sheet, state, done)
            except ResultsUnavailable:
                RUN["fails"] = 0
                save_state(state)
                save_outputs(sheet, state)
                print(f"\n[{time.strftime('%d.%m %H:%M')}] Страницы результатов перестали "
                      f"загружаться — похоже, их убрали с сайта. Перехожу в ожидание.")
                continue

            remaining = count_remaining(state, done)
            if remaining == 0:
                print("\n✅ Сбор завершён, все страницы загружены.")
                break
            if not RUN["wait"]:
                print(f"\n⚠ Сбор завершён, но {remaining} страниц не загрузились. "
                      f"Запустите скрипт ещё раз позже — он догрузит только их.")
                break
            if remaining == last_remaining:
                print(f"\n⚠ Сбор завершён. {remaining} страниц так и не загрузились, хотя "
                      f"результаты на сайте есть, — вероятно, на этих страницах нет данных.")
                break
            last_remaining = remaining
            print(f"\nОсталось незагруженных страниц: {remaining}. Попробую ещё раз.")
    except KeyboardInterrupt:
        print("\n⏸ Остановлено пользователем. Запустите скрипт снова, чтобы продолжить.")
    finally:
        save_state(state)
        save_outputs(sheet, state)
        try:
            driver.quit()
        except Exception:
            pass
        print("Браузер закрыт. Прогресс сохранён в parser_state.json.")


if __name__ == "__main__":
    main()
