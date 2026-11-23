// mend: applies an AI-written edit (unified diff, SEARCH/REPLACE blocks, V4A or JSON edits) to the tree of text files
// rooted at the working directory, as SPEC.md specifies. Node 22 and its standard library only:
//
//     node main.ts [--format=NAME] [--check] [--strict] [PATCH]
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): that hand-over and runner.ts are kept exactly as the kit has them.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

// ---------------------------------------------------------------------------------------------------------------
// Results and failures

/** Exit 2: one line, nothing written. */
class Stop {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One edit failed with an SPEC.md section 2 code; the path is the one the failure concerns. */
type Code = 'no-match' | 'ambiguous' | 'missing' | 'exists' | 'unsafe';

class EditError {
  readonly code: Code;
  readonly path: string;
  constructor(code: Code, path: string) {
    this.code = code;
    this.path = path;
  }
}

const parseError = (lineNo: number): Stop => new Stop(`error: parse ${lineNo}`);

// ---------------------------------------------------------------------------------------------------------------
// Text, lines and paths (SPEC.md section 3)

const isBlank = (s: string): boolean => /^\s*$/.test(s);

/** A patch's lines: split at \n, one trailing \r dropped from each, no empty piece after a final \n. */
function splitPatch(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (parts[parts.length - 1] === '') parts.pop();
  return parts.map((p) => (p.endsWith('\r') ? p.slice(0, -1) : p));
}

/** A text file seen as lines: its break, its lines, and whether it ends with a break. */
interface Doc {
  br: '\n' | '\r\n';
  lines: string[];
  final: boolean;
}

function breakOf(text: string): '\n' | '\r\n' {
  const nl = text.indexOf('\n');
  return nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
}

function toDoc(text: string): Doc {
  const br = breakOf(text);
  if (text === '') return { br, lines: [], final: false };
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { br, lines, final };
}

function fromDoc(doc: Doc): string {
  if (doc.lines.length === 0) return '';
  return doc.lines.join(doc.br) + (doc.final ? doc.br : '');
}

/** A file a patch creates: LF breaks, a final break unless told otherwise. */
function newFile(lines: string[], final = true): string {
  return fromDoc({ br: '\n', lines, final });
}

function isSafe(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((seg) => seg !== '' && seg !== '.' && seg !== '..');
}

function requireSafe(...paths: string[]): void {
  for (const p of paths) if (!isSafe(p)) throw new EditError('unsafe', p);
}

// ---------------------------------------------------------------------------------------------------------------
// Matching lines at three tiers (SPEC.md section 5)

const trimEndWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => trimEndWs(s).replace(/^[ \t]+/, '');
const leadWs = (s: string): string => /^[ \t]*/.exec(s)![0];

/** Tier 0 compares lines as they are, tier 1 without trailing spaces/tabs, tier 2 without leading ones too. */
const TIERS: ReadonlyArray<(s: string) => string> = [(s) => s, trimEndWs, trimWs];

/** A line as the given tier compares it. */
const normalise = (line: string, tier: number): string => TIERS[tier]!(line);

/** Tier 2, the one at which N is re-indented (SPEC.md section 5). */
const REINDENT_TIER = 2;

let strictMode = false;
/** `--strict` tries tier 0 alone; otherwise all three tiers. */
const tierCount = (): number => (strictMode ? 1 : TIERS.length);

/** Every position i at which `old` matches `lines` at the given tier (occurrences may overlap). */
function occurrences(lines: string[], old: string[], tier: number, from = 0): number[] {
  const want = old.map((l) => normalise(l, tier));
  const out: number[] = [];
  for (let i = Math.max(0, from); i + want.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < want.length; j++) {
      if (normalise(lines[i + j]!, tier) !== want[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/**
 * The first tier at which `accept` keeps at least one occurrence of `old`, with the occurrences it keeps, or null
 * when there is none at any tier.
 */
function locate(
  lines: string[],
  old: string[],
  from = 0,
  accept: (i: number) => boolean = () => true,
): { tier: number; at: number[] } | null {
  for (let tier = 0; tier < tierCount(); tier++) {
    const at = occurrences(lines, old, tier, from).filter(accept);
    if (at.length > 0) return { tier, at };
  }
  return null;
}

/** A line of N: its text and, for a context line, its index in O. */
interface NewLine {
  text: string;
  ctx: number | null;
}

/**
 * The lines that replace O matched at `pos` and `tier`: context lines are the file's own, and at tier 2 every other
 * line has O's leading indentation swapped for the file's.
 */
function replacement(lines: string[], pos: number, tier: number, old: string[], neu: NewLine[]): string[] {
  const fileIndent = old.length > 0 ? leadWs(lines[pos]!) : '';
  const patchIndent = old.length > 0 ? leadWs(old[0]!) : '';
  return neu.map((n) => {
    if (n.ctx !== null) return lines[pos + n.ctx]!;
    if (tier === REINDENT_TIER && !isBlank(n.text) && n.text.startsWith(patchIndent)) {
      return fileIndent + n.text.slice(patchIndent.length);
    }
    return n.text;
  });
}

const plain = (texts: string[]): NewLine[] => texts.map((text) => ({ text, ctx: null }));

// ---------------------------------------------------------------------------------------------------------------
// The tree as the edits leave it (SPEC.md section 10)

/** Every edit reads and writes the tree through this; nothing touches the disk until every edit has succeeded. */
class Tree {
  private readonly disk = new Map<string, string | null>();
  private staged = new Map<string, string | null>();
  /** The move edits that succeeded, in order: [old, new]. */
  private moved: Array<[string, string]> = [];

  /** The file's text before the patch, or null when there is no regular file at the path. */
  before(p: string): string | null {
    if (!this.disk.has(p)) {
      let text: string | null = null;
      try {
        if (statSync(p).isFile()) text = readFileSync(p, 'utf8');
      } catch {
        text = null;
      }
      this.disk.set(p, text);
    }
    return this.disk.get(p)!;
  }

  read(p: string): string | null {
    return this.staged.has(p) ? this.staged.get(p)! : this.before(p);
  }

  exists(p: string): boolean {
    return this.read(p) !== null;
  }

  write(p: string, text: string | null): void {
    this.staged.set(p, text);
  }

  move(from: string, to: string, text: string): void {
    this.staged.set(from, null);
    this.staged.set(to, text);
    this.moved.push([from, to]);
  }

  /** Runs one edit; when it fails, the tree is left as it was before it. */
  attempt(edit: () => void): EditError | null {
    const staged = new Map(this.staged);
    const moved = this.moved.length;
    try {
      edit();
      return null;
    } catch (e) {
      if (!(e instanceof EditError)) throw e;
      this.staged = staged;
      this.moved.length = moved;
      return e;
    }
  }

  /** The status lines of section 2, in byte order of their paths, and the writes that make them so. */
  summary(): { rows: string[]; deletes: string[]; writes: Array<[string, string]> } {
    const changed = new Map<string, 'A' | 'D' | 'M'>();
    const deletes: string[] = [];
    const writes: Array<[string, string]> = [];
    for (const [p, now] of this.staged) {
      const was = this.before(p);
      if (was === now) continue;
      if (now === null) {
        changed.set(p, 'D');
        deletes.push(p);
      } else {
        changed.set(p, was === null ? 'A' : 'M');
        writes.push([p, now]);
      }
    }
    const rows: Array<{ key: string; line: string }> = [];
    for (const [from, to] of this.moved) {
      if (changed.get(from) === 'D' && changed.get(to) === 'A') {
        changed.delete(from);
        changed.delete(to);
        rows.push({ key: to, line: `R ${from} -> ${to}` });
      }
    }
    for (const [p, kind] of changed) rows.push({ key: p, line: `${kind} ${p}` });
    rows.sort((a, b) => Buffer.compare(Buffer.from(a.key, 'utf8'), Buffer.from(b.key, 'utf8')));
    return { rows: rows.map((r) => r.line), deletes, writes };
  }
}

/** The text of a file the edit needs to exist. */
function mustExist(tree: Tree, p: string): string {
  const text = tree.read(p);
  if (text === null) throw new EditError('missing', p);
  return text;
}

function mustBeAbsent(tree: Tree, p: string): void {
  if (tree.exists(p)) throw new EditError('exists', p);
}

type Edit = (tree: Tree) => void;

// ---------------------------------------------------------------------------------------------------------------
// Detecting the format (SPEC.md section 4)

type Format = 'unified' | 'search-replace' | 'v4a' | 'json';

function detectFormat(lines: string[]): Format | null {
  const first = lines.find((l) => !isBlank(l));
  if (first === undefined) return null;
  if (first.trim() === '*** Begin Patch') return 'v4a';
  const lead = first.trimStart()[0];
  if (lead === '[' || lead === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) return 'unified';
    if (l.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ')) return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------------------------------------------------------
// JSON edits (SPEC.md section 9)

const isObject = (v: unknown): v is Record<string, unknown> => v !== null && typeof v === 'object' && !Array.isArray(v);

/** A CRLF file's text read with every \r\n as \n, and a way back. */
function lfView(text: string): { lf: (s: string) => string; back: (s: string) => string } {
  if (breakOf(text) === '\r\n') return { lf: (s) => s.replaceAll('\r\n', '\n'), back: (s) => s.replaceAll('\n', '\r\n') };
  return { lf: (s) => s, back: (s) => s };
}

/** One edit object as an edit, or null when it is a parse fault. */
function jsonEdit(v: unknown): Edit | null {
  if (!isObject(v) || typeof v.path !== 'string') return null;
  const path = v.path;
  switch (v.command) {
    case 'create': {
      const body = v.file_text;
      if (typeof body !== 'string') return null;
      return (tree) => {
        requireSafe(path);
        mustBeAbsent(tree, path);
        tree.write(path, body);
      };
    }
    case 'str_replace': {
      const oldStr = v.old_str;
      const newStr = v.new_str === undefined ? '' : v.new_str;
      if (typeof oldStr !== 'string' || oldStr === '' || typeof newStr !== 'string') return null;
      return (tree) => {
        requireSafe(path);
        const text = mustExist(tree, path);
        const { lf, back } = lfView(text);
        const hay = lf(text);
        const needle = lf(oldStr);
        const first = hay.indexOf(needle);
        if (first < 0) throw new EditError('no-match', path);
        if (hay.indexOf(needle, first + 1) >= 0) throw new EditError('ambiguous', path);
        tree.write(path, back(hay.slice(0, first) + lf(newStr) + hay.slice(first + needle.length)));
      };
    }
    case 'insert': {
      const at = v.insert_line;
      const newStr = v.new_str;
      if (typeof at !== 'number' || !Number.isInteger(at) || typeof newStr !== 'string') return null;
      const added = splitPatch(newStr);
      return (tree) => {
        requireSafe(path);
        const doc = toDoc(mustExist(tree, path));
        if (at < 0 || at > doc.lines.length) throw new EditError('no-match', path);
        doc.lines.splice(at, 0, ...added);
        tree.write(path, fromDoc(doc));
      };
    }
    default:
      return null;
  }
}

/** JSON edits parser (SPEC.md section 9): one JSON array of edit objects, or JSON Lines of one object each. */
function readJson(text: string, lines: string[]): Edit[] {
  const start = lines.findIndex((l) => !isBlank(l));
  if (start < 0) throw parseError(1);
  if (lines[start]!.trimStart().startsWith('[')) {
    let value: unknown;
    try {
      value = JSON.parse(text);
    } catch {
      throw parseError(start + 1);
    }
    if (!Array.isArray(value)) throw parseError(start + 1);
    return value.map((item) => jsonEdit(item) ?? (() => { throw parseError(start + 1); })());
  }
  const edits: Edit[] = [];
  lines.forEach((l, i) => {
    if (isBlank(l)) return;
    let edit: Edit | null = null;
    try {
      edit = jsonEdit(JSON.parse(l));
    } catch {
      edit = null;
    }
    if (edit === null) throw parseError(i + 1);
    edits.push(edit);
  });
  return edits;
}

// ---------------------------------------------------------------------------------------------------------------
// Unified diffs (SPEC.md section 6)

interface BodyLine {
  kind: ' ' | '-' | '+';
  text: string;
  /** A `\` line follows this one. */
  noEol: boolean;
  /** The patch line was empty (a context line without its leading space). */
  bare: boolean;
}

interface Hunk {
  a: number;
  body: BodyLine[];
}

interface Section {
  gitOld?: string;
  gitNew?: string;
  /** From the `---`/`+++` pair: undefined when there is none, null for /dev/null. */
  minus?: string | null;
  plus?: string | null;
  renameFrom?: string;
  renameTo?: string;
  creation: boolean;
  deletion: boolean;
  /** Whether the section came from a `diff --git` line and has not yet had its `---`/`+++` pair. */
  awaitingPair: boolean;
  hunks: Hunk[];
}

const HUNK_HEADER = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;
const GIT_HEADER = /^diff --git a\/(.+?) b\/(.+)$/;
/** `--- ` and `+++ ` are both four characters: the path is the text after them (SPEC.md section 6). */
const FILE_HEADER_PREFIX = '--- ';

/** The path of a `---` or `+++` line: up to the first tab, trimmed, without a/ or b/; null for /dev/null. */
function headerPath(line: string): string | null {
  let p = line.slice(FILE_HEADER_PREFIX.length);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.replace(/^ +/, '').replace(/ +$/, '');
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice('a/'.length);
  return p;
}

const isPairAt = (lines: string[], i: number): boolean =>
  lines[i]!.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ');

/** Unified diff parser (SPEC.md section 6): sections, their headers and their hunks, one edit per section. */
function parseUnified(lines: string[]): Section[] {
  const sections: Section[] = [];
  let current: Section | null = null;
  /** Before the current section's first hunk. */
  let inHeader = false;
  const open = (s: Partial<Section>): Section => {
    const section: Section = { creation: false, deletion: false, awaitingPair: false, hunks: [], ...s };
    sections.push(section);
    inHeader = true;
    return section;
  };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = GIT_HEADER.exec(line);
      if (m === null) throw parseError(i + 1);
      current = open({ gitOld: m[1]!, gitNew: m[2]!, awaitingPair: true });
      i += 1;
    } else if (isPairAt(lines, i)) {
      if (current === null || !inHeader || !current.awaitingPair) current = open({});
      current.minus = headerPath(line);
      current.plus = headerPath(lines[i + 1]!);
      current.awaitingPair = false;
      i += 2; // the `---` line and its `+++` line
    } else if (line.startsWith('--- ') && current !== null && inHeader) {
      // A lone `---` in a header is an error at the line after it: 0-based i + 1, so 1-based i + 2.
      throw parseError(i + 2);
    } else if (line.startsWith('@@')) {
      const m = HUNK_HEADER.exec(line);
      if (m === null || current === null) throw parseError(i + 1);
      i += 1;
      const body: BodyLine[] = [];
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ') || isPairAt(lines, i)) break;
        if (b === '') body.push({ kind: ' ', text: '', noEol: false, bare: true });
        else if (b[0] === ' ' || b[0] === '-' || b[0] === '+') body.push({ kind: b[0], text: b.slice(1), noEol: false, bare: false });
        else if (b[0] === '\\') {
          if (body.length > 0) body[body.length - 1]!.noEol = true;
        } else break;
        i += 1;
      }
      // Empty lines at the end of a body are not part of it (a `\` line after one still marks it).
      while (body.length > 0) {
        const last = body[body.length - 1]!;
        if (last.bare && !last.noEol) body.pop();
        else break;
      }
      current.hunks.push({ a: Number(m[1]), body });
      inHeader = false;
    } else {
      if (current !== null && inHeader) {
        if (line.startsWith('rename from ')) current.renameFrom = line.slice('rename from '.length);
        else if (line.startsWith('rename to ')) current.renameTo = line.slice('rename to '.length);
        else if (line.startsWith('new file mode')) current.creation = true;
        else if (line.startsWith('deleted file mode')) current.deletion = true;
      }
      i += 1;
    }
  }
  return sections;
}

/** O and N of a hunk, and whether a `\` line follows N's last line. */
function hunkSides(h: Hunk): { old: string[]; neu: NewLine[]; noEolAtEnd: boolean } {
  const old: string[] = [];
  const neu: NewLine[] = [];
  let noEolAtEnd = false;
  for (const b of h.body) {
    if (b.kind === ' ') {
      neu.push({ text: b.text, ctx: old.length });
      old.push(b.text);
    } else if (b.kind === '-') {
      old.push(b.text);
      continue;
    } else {
      neu.push({ text: b.text, ctx: null });
    }
    noEolAtEnd = b.noEol;
  }
  return { old, neu, noEolAtEnd };
}

/** Applies a section's hunks in order to `doc`, failing with `no-match` against `path`. */
function applyHunks(doc: Doc, hunks: Hunk[], path: string): void {
  let drift = 0;
  for (const h of hunks) {
    const { old, neu, noEolAtEnd } = hunkSides(h);
    let pos: number;
    let written: string[];
    if (old.length === 0) {
      pos = Math.min(Math.max(h.a + drift, 0), doc.lines.length);
      written = neu.map((n) => n.text);
    } else {
      const found = locate(doc.lines, old);
      if (found === null) throw new EditError('no-match', path);
      const target = h.a - 1 + drift;
      pos = found.at[0]!;
      for (const at of found.at) if (Math.abs(at - target) < Math.abs(pos - target)) pos = at;
      written = replacement(doc.lines, pos, found.tier, old, neu);
    }
    const toEnd = pos + old.length === doc.lines.length;
    doc.lines.splice(pos, old.length, ...written);
    if (toEnd) doc.final = !noEolAtEnd;
    drift += neu.length - old.length;
  }
}

function sectionEdit(s: Section): Edit {
  const oldPath = s.minus !== undefined ? s.minus : (s.renameFrom ?? s.gitOld ?? null);
  const newPath = s.plus !== undefined ? s.plus : (s.renameTo ?? s.gitNew ?? null);
  const creation = s.creation || (s.minus === null && !s.deletion);
  const deletion = !creation && (s.deletion || s.plus === null);

  if (creation) {
    const target = newPath ?? oldPath ?? '';
    return (tree) => {
      requireSafe(target);
      mustBeAbsent(tree, target);
      const added: string[] = [];
      let noEol = false;
      for (const h of s.hunks) {
        for (const b of h.body) {
          if (b.kind !== '+') continue;
          added.push(b.text);
          noEol = b.noEol;
        }
      }
      tree.write(target, newFile(added, !noEol));
    };
  }
  if (deletion) {
    const target = oldPath ?? newPath ?? '';
    return (tree) => {
      requireSafe(target);
      mustExist(tree, target);
      tree.write(target, null);
    };
  }
  const from = oldPath ?? '';
  const to = newPath ?? from;
  if (from !== to) {
    return (tree) => {
      requireSafe(from, to);
      const doc = toDoc(mustExist(tree, from));
      mustBeAbsent(tree, to);
      applyHunks(doc, s.hunks, from);
      tree.move(from, to, fromDoc(doc));
    };
  }
  return (tree) => {
    requireSafe(from);
    const doc = toDoc(mustExist(tree, from));
    applyHunks(doc, s.hunks, from);
    tree.write(from, fromDoc(doc));
  };
}

function readUnified(lines: string[]): Edit[] {
  return parseUnified(lines).map(sectionEdit);
}

// ---------------------------------------------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC.md section 7)

interface Block {
  path: string;
  old: string[];
  neu: string[];
}

const isMarker = (line: string, marker: string): boolean => line.trimEnd() === marker;

/** SEARCH/REPLACE blocks parser (SPEC.md section 7): path line, SEARCH, =======, REPLACE; one edit per block. */
function parseSearchReplace(lines: string[]): Block[] {
  const blocks: Block[] = [];
  /** Where the lines that may hold the next block's path begin. */
  let regionStart = 0;
  let i = 0;
  while (i < lines.length) {
    if (!isMarker(lines[i]!, '<<<<<<< SEARCH')) {
      i += 1;
      continue;
    }
    const search = i;
    let path: string | null = null;
    for (let k = search - 1; k >= regionStart; k--) {
      const t = lines[k]!.trim();
      if (t !== '' && !t.startsWith('```')) {
        path = t;
        break;
      }
    }
    if (path === null) {
      if (blocks.length === 0) throw parseError(search + 1);
      path = blocks[blocks.length - 1]!.path;
    }
    let divider = -1;
    for (let k = search + 1; k < lines.length; k++) {
      if (isMarker(lines[k]!, '=======')) {
        divider = k;
        break;
      }
    }
    let end = -1;
    if (divider >= 0) {
      for (let k = divider + 1; k < lines.length; k++) {
        if (isMarker(lines[k]!, '>>>>>>> REPLACE')) {
          end = k;
          break;
        }
      }
    }
    if (end < 0) throw parseError(search + 1);
    blocks.push({ path, old: lines.slice(search + 1, divider), neu: lines.slice(divider + 1, end) });
    regionStart = end + 1;
    i = end + 1;
  }
  return blocks;
}

function blockEdit(b: Block): Edit {
  return (tree) => {
    requireSafe(b.path);
    if (b.old.length === 0) {
      mustBeAbsent(tree, b.path);
      tree.write(b.path, newFile(b.neu));
      return;
    }
    const doc = toDoc(mustExist(tree, b.path));
    const found = locate(doc.lines, b.old);
    if (found === null) throw new EditError('no-match', b.path);
    if (found.at.length > 1) throw new EditError('ambiguous', b.path);
    const pos = found.at[0]!;
    doc.lines.splice(pos, b.old.length, ...replacement(doc.lines, pos, found.tier, b.old, plain(b.neu)));
    tree.write(b.path, fromDoc(doc));
  };
}

function readSearchReplace(lines: string[]): Edit[] {
  return parseSearchReplace(lines).map(blockEdit);
}

// ---------------------------------------------------------------------------------------------------------------
// V4A patches (SPEC.md section 8)

interface Chunk {
  anchor: string | null;
  body: Array<{ kind: ' ' | '-' | '+'; text: string }>;
  eof: boolean;
}

type V4aSection =
  | { kind: 'add'; path: string; lines: string[] }
  | { kind: 'delete'; path: string }
  | { kind: 'update'; path: string; moveTo: string | null; chunks: Chunk[] };

const V4A_STARTS = ['*** Add File: ', '*** Delete File: ', '*** Update File: '] as const;

/** V4A patch parser (SPEC.md section 8): Add/Delete/Update File sections between Begin and End Patch. */
function parseV4a(lines: string[]): V4aSection[] {
  const nonBlank = lines.map((l, i) => (isBlank(l) ? -1 : i)).filter((i) => i >= 0);
  if (nonBlank.length === 0) throw parseError(1);
  const begin = nonBlank[0]!;
  const end = nonBlank[nonBlank.length - 1]!;
  if (lines[begin]!.trim() !== '*** Begin Patch') throw parseError(begin + 1);
  // A missing End Patch is reported one past the last patch line (SPEC.md section 8).
  if (lines[end]!.trim() !== '*** End Patch' || end === begin) throw parseError(lines.length + 1);

  // Split the lines between the markers into sections: [header line index, body line indexes].
  const raw: Array<{ head: number; body: number[] }> = [];
  for (let i = begin + 1; i < end; i++) {
    const line = lines[i]!;
    if (V4A_STARTS.some((s) => line.startsWith(s))) raw.push({ head: i, body: [] });
    else if (raw.length > 0) raw[raw.length - 1]!.body.push(i);
    else if (!isBlank(line)) throw parseError(i + 1);
  }

  return raw.map(({ head, body }) => {
    while (body.length > 0 && isBlank(lines[body[body.length - 1]!]!)) body.pop();
    const line = lines[head]!;
    const start = V4A_STARTS.find((s) => line.startsWith(s))!;
    const path = line.slice(start.length).trim();
    if (start === '*** Add File: ') {
      const fileLines = body.map((k) => {
        const b = lines[k]!;
        if (b === '') return '';
        if (b.startsWith('+')) return b.slice(1);
        throw parseError(k + 1);
      });
      return { kind: 'add', path, lines: fileLines };
    }
    if (start === '*** Delete File: ') {
      if (body.length > 0) throw parseError(body[0]! + 1);
      return { kind: 'delete', path };
    }
    let moveTo: string | null = null;
    let from = 0;
    if (body.length > 0 && lines[body[0]!]!.startsWith('*** Move to: ')) {
      moveTo = lines[body[0]!]!.slice('*** Move to: '.length).trim();
      from = 1;
    }
    const chunks: Chunk[] = [];
    let chunk: Chunk | null = null;
    for (const k of body.slice(from)) {
      const b = lines[k]!;
      if (b.startsWith('@@')) {
        const anchor = b.slice('@@'.length).trim();
        chunk = { anchor: anchor === '' ? null : anchor, body: [], eof: false };
        chunks.push(chunk);
      } else if (b.trimEnd() === '*** End of File') {
        if (chunk === null) throw parseError(k + 1);
        chunk.eof = true;
        chunk = null;
      } else if (b === '' || b[0] === ' ' || b[0] === '-' || b[0] === '+') {
        if (chunk === null) {
          if (chunks.length > 0) throw parseError(k + 1);
          chunk = { anchor: null, body: [], eof: false };
          chunks.push(chunk);
        }
        chunk.body.push(b === '' ? { kind: ' ', text: '' } : { kind: b[0] as ' ' | '-' | '+', text: b.slice(1) });
      } else {
        throw parseError(k + 1);
      }
    }
    if (chunks.length === 0 && moveTo === null) throw parseError(head + 1);
    return { kind: 'update', path, moveTo, chunks };
  });
}

/** Applies one chunk at the cursor and returns the new cursor. */
function applyChunk(doc: Doc, c: Chunk, cursor: number, path: string): number {
  if (c.anchor !== null) {
    const found = locate(doc.lines, [c.anchor], cursor);
    if (found === null) throw new EditError('no-match', path);
    cursor = found.at[0]! + 1;
  }
  const old: string[] = [];
  const neu: NewLine[] = [];
  for (const b of c.body) {
    if (b.kind === ' ') {
      neu.push({ text: b.text, ctx: old.length });
      old.push(b.text);
    } else if (b.kind === '-') old.push(b.text);
    else neu.push({ text: b.text, ctx: null });
  }
  if (old.length === 0) {
    const at = c.eof ? doc.lines.length : Math.min(cursor, doc.lines.length);
    doc.lines.splice(at, 0, ...neu.map((n) => n.text));
    return at + neu.length;
  }
  const endsAtLast = (i: number): boolean => i + old.length === doc.lines.length;
  const found = locate(doc.lines, old, cursor, c.eof ? endsAtLast : undefined);
  if (found === null) throw new EditError('no-match', path);
  const pos = found.at[0]!;
  const written = replacement(doc.lines, pos, found.tier, old, neu);
  doc.lines.splice(pos, old.length, ...written);
  return pos + written.length;
}

function v4aEdit(s: V4aSection): Edit {
  switch (s.kind) {
    case 'add':
      return (tree) => {
        requireSafe(s.path);
        mustBeAbsent(tree, s.path);
        tree.write(s.path, newFile(s.lines));
      };
    case 'delete':
      return (tree) => {
        requireSafe(s.path);
        mustExist(tree, s.path);
        tree.write(s.path, null);
      };
    case 'update':
      return (tree) => {
        requireSafe(s.path, ...(s.moveTo === null ? [] : [s.moveTo]));
        const doc = toDoc(mustExist(tree, s.path));
        if (s.moveTo !== null) mustBeAbsent(tree, s.moveTo);
        let cursor = 0;
        for (const c of s.chunks) cursor = applyChunk(doc, c, cursor, s.path);
        if (s.moveTo === null) tree.write(s.path, fromDoc(doc));
        else tree.move(s.path, s.moveTo, fromDoc(doc));
      };
  }
}

function readV4a(lines: string[]): Edit[] {
  return parseV4a(lines).map(v4aEdit);
}

// ---------------------------------------------------------------------------------------------------------------
// The command line (SPEC.md sections 1 and 2)

const FORMAT_NAMES = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

interface Options {
  format: string;
  check: boolean;
  strict: boolean;
  patch: string | null;
}

function parseArgs(args: string[]): Options {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const positional: string[] = [];
  let optionsEnded = false;
  for (const a of args) {
    if (optionsEnded || a === '-' || !a.startsWith('-')) {
      positional.push(a);
    } else if (a === '--') {
      optionsEnded = true;
    } else if (a.startsWith('--format=') && format === null && FORMAT_NAMES.includes(a.slice('--format='.length))) {
      format = a.slice('--format='.length);
    } else if (a === '--check' && !check) {
      check = true;
    } else if (a === '--strict' && !strict) {
      strict = true;
    } else {
      throw new Stop('error: usage');
    }
  }
  if (positional.length > 1) throw new Stop('error: usage');
  const patch = positional.length === 0 || positional[0] === '-' ? null : positional[0]!;
  return { format: format ?? 'auto', check, strict, patch };
}

function readPatch(file: string | null): string {
  if (file !== null) {
    try {
      return readFileSync(file, 'utf8');
    } catch {
      throw new Stop('error: no-patch');
    }
  }
  try {
    return readFileSync(0, 'utf8');
  } catch {
    return '';
  }
}

function readEdits(format: Format, text: string, lines: string[]): Edit[] {
  switch (format) {
    case 'json':
      return readJson(text, lines);
    case 'unified':
      return readUnified(lines);
    case 'search-replace':
      return readSearchReplace(lines);
    case 'v4a':
      return readV4a(lines);
  }
}

function run(args: string[]): { code: number; out: string[] } {
  let opts: Options;
  let edits: Edit[];
  try {
    opts = parseArgs(args);
    const text = readPatch(opts.patch);
    const lines = splitPatch(text);
    const format = opts.format === 'auto' ? detectFormat(lines) : (opts.format as Format);
    if (format === null) throw new Stop('error: format');
    edits = readEdits(format, text, lines);
    // A patch in which the reader finds no edit at all is `error: parse 1` (SPEC.md section 2).
    if (edits.length === 0) throw parseError(1);
  } catch (e) {
    if (e instanceof Stop) return { code: 2, out: [e.line] };
    throw e;
  }
  strictMode = opts.strict;

  const tree = new Tree();
  const failures: EditError[] = [];
  for (const edit of edits) {
    const failure = tree.attempt(() => edit(tree));
    if (failure !== null) failures.push(failure);
  }
  if (failures.length > 0) {
    return {
      code: 1,
      out: [...failures.map((f) => `error: ${f.code} ${f.path}`), `failed: ${failures.length} of ${edits.length} edits`],
    };
  }

  const { rows, deletes, writes } = tree.summary();
  if (!opts.check) {
    for (const p of deletes) rmSync(p, { force: true });
    for (const [p, text] of writes) {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, text);
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
