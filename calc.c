// Name: Yusif Surname: Gahramanli Student ID: 251ADB086
// https://github.com/Yuska2325/calc-lab-home
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used: Gemini https://share.gemini.google/H6zcTj9Mjw79  for the parser structure, the integer and float handling, and the file and command-line handling;
#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#define STUDENT_NAME "yusif"
#define STUDENT_LASTNAME "gahramanli"
#define STUDENT_ID "251ADB086"
#define MAX_DEPTH 5000
#define LL_MIN (-9223372036854775807LL - 1)
typedef struct{
    int is_float;
    long long i;
    double d;
}Value;
typedef enum{
    T_INT, T_FLOAT, T_PLUS, T_MINUS, T_MUL, T_DIV, T_POW, T_LP, T_RP, T_EOL, T_BAD
}TokType;
typedef struct{
    TokType type;
    size_t pos;
    Value val;
}Token;
typedef struct{
    const char *src;
    size_t cur;
    size_t line_end;
    Token tok;
    size_t err_pos;
    int depth;
    char *scratch;
    size_t scratch_cap;
}Parser;
typedef struct{
    Value v;
    size_t start;
    size_t op;
}PowItem;
static PowItem *pow_stack = NULL;
static size_t pow_sp = 0, pow_cap = 0;
static int parse_expr(Parser *P, Value *out);
static void advance(Parser *P){
    const char *s = P->src;
    while (P->cur < P->line_end && (s[P->cur] == ' ' || s[P->cur] == '\t')){
         P->cur++;
    }
    Token *t = &P->tok;
    t->pos = P->cur;
    if (P->cur >= P->line_end){
        t->type = T_EOL;
        return;
    }
    char c = s[P->cur];
    switch (c){
    case '+': t->type = T_PLUS; P->cur++; return;
    case '-': t->type = T_MINUS; P->cur++; return;
    case '/': t->type = T_DIV; P->cur++; return;
    case '(': t->type = T_LP; P->cur++; return;
    case ')': t->type = T_RP; P->cur++; return;
    case '*':
        if (P->cur + 1 < P->line_end && s[P->cur + 1] == '*') {
            t->type = T_POW;
            P->cur += 2;
        } else {
            t->type = T_MUL;
            P->cur++;
        }
        return;
    default:
        break;
    }
    if (isdigit((unsigned char)c)){
        size_t start = P->cur;
        unsigned long long acc = 0; // unsigned: wrap-around is defined, no UB
        while (P->cur < P->line_end && isdigit((unsigned char)s[P->cur])) {
            acc = acc * 10u + (unsigned long long)(s[P->cur] - '0');
            P->cur++;
        }
        // A float needs '.' followed by at least one digit. For "5." we stop
        // after the 5; the '.' is then left as the next token, which turns
        // into T_BAD, so the error lands on the '.' as required.
        if (P->cur + 1 < P->line_end && s[P->cur] == '.' &&
            isdigit((unsigned char)s[P->cur + 1])){
            P->cur++;
            while (P->cur < P->line_end && isdigit((unsigned char)s[P->cur]))
                P->cur++;
            size_t n = P->cur - start;
            // strtod needs a NUL-terminated string, but our text lives in the
            // big file buffer, so copy just this literal into a small reusable
            // buffer (and keep strtod from reading on into e.g. "1.5e3").
            if (n + 1 > P->scratch_cap){
                size_t cap = (n + 1) * 2;
                char *nb = realloc(P->scratch, cap);
                if (!nb) {
                    fprintf(stderr, "calc: out of memory\n");
                    exit(1);
                }
                P->scratch = nb;
                P->scratch_cap = cap;
            }
            memcpy(P->scratch, s + start, n);
            P->scratch[n] = '\0';
            double d = strtod(P->scratch, NULL);
            if (!isfinite(d)) { // literal too large for a double: invalid
                t->type = T_BAD;
                t->pos = start;
                return;
            }
            t->type = T_FLOAT;
            t->val.is_float = 1;
            t->val.d = d;
            t->val.i = 0;
        } else{
            t->type = T_INT;
            t->val.is_float = 0;
            t->val.i = (long long)acc;
            t->val.d = 0.0;
        }
        return;
    }
    // Anything else ('#' not at line start, '.', letters, '\r', ...) is
    // invalid. Consume it so the lexer always makes progress.
    t->type = T_BAD;
    P->cur++;
}
static int fail(Parser *P, size_t pos) {
    P->err_pos = pos;
    return -1;
}

// Integer power by repeated squaring: O(log exp) even for huge exponents such
// as 1 ** 1000000. Done in unsigned arithmetic so wrap-around is defined.
// The last squaring is skipped because it could overflow without being needed.
static long long ipow(long long base, long long exp) {
    unsigned long long r = 1, b = (unsigned long long)base;
    while (exp > 0) {
        if (exp & 1) r *= b;
        exp >>= 1;
        if (exp) b *= b;
    }
    return (long long)r;
}

// Apply one binary operator. op_pos is where the operator is written and
// rhs_pos where its right operand starts; they are the two positions the lab
// uses for errors:
//   * division by zero and negative integer exponent -> start of the right
//     operand (that operand is what is wrong),
//   * infinite/NaN float result -> the operator (no single operand is wrong:
//     e.g. (0-8) ** 0.5 has fine operands but no real result).
static int apply(Parser *P, TokType op, Value a, Value b,
                 size_t op_pos, size_t rhs_pos, Value *out) {
    if (!a.is_float && !b.is_float) {
        unsigned long long x = (unsigned long long)a.i, y = (unsigned long long)b.i;
        out->is_float = 0;
        out->d = 0.0;
        switch (op) {
        case T_PLUS: out->i = (long long)(x + y); return 0;
        case T_MINUS: out->i = (long long)(x - y); return 0;
        case T_MUL: out->i = (long long)(x * y); return 0;
        case T_DIV:
            if (b.i == 0)return fail(P, rhs_pos);
            if (a.i == LL_MIN && b.i == -1) out->i = a.i;
            else out->i = a.i / b.i;
            return 0;
        case T_POW:
            if (b.i < 0) return fail(P, rhs_pos);
            out->i = ipow(a.i, b.i);
            return 0;
        default: return fail(P, op_pos);
        }
    }
    // At least one operand is a float: promote the other one and compute in
    // double, so 7 / 2.0 is 3.5 and 0.5 ** (0 - 1) is 2.
    double x = a.is_float ? a.d : (double)a.i;
    double y = b.is_float ? b.d : (double)b.i;
    double r;
    switch (op) {
    case T_PLUS: r = x + y; break;
    case T_MINUS: r = x - y; break;
    case T_MUL: r = x * y; break;
    case T_DIV:
        if (y == 0.0) return fail(P, rhs_pos); // float division by zero is an error too
        r = x / y;
        break;
    case T_POW: r = pow(x, y); break;
    default: return fail(P, op_pos);
    }
    if (!isfinite(r)) return fail(P, op_pos); // inf or NaN
    out->is_float = 1;
    out->d = r;
    out->i = 0;
    return 0;
}
static int parse_primary(Parser *P, Value *out) {
    if (P->tok.type == T_INT || P->tok.type == T_FLOAT) {
        *out = P->tok.val;
        advance(P);
        return 0;
    }
    if (P->tok.type == T_LP) {
        if (P->depth >= MAX_DEPTH) return fail(P, P->tok.pos);
        advance(P);
        P->depth++;
        if (parse_expr(P, out) != 0) return -1;
        P->depth--;
        if (P->tok.type != T_RP) return fail(P, P->tok.pos);
        advance(P);
        return 0;
    }
    return fail(P, P->tok.pos);
}
static int power(Parser *P, Value *out) {
    size_t base = pow_sp;
#define PUSH_OPERAND(OPPOS)                                                    \
    do{                                                                       \
        size_t st_ = P->tok.pos;                                               \
        Value tmp_;                                                            \
        if (parse_primary(P, &tmp_) != 0) {                                    \
            pow_sp = base;                                                     \
            return -1;                                                         \
        }                                                                      \
        if (pow_sp == pow_cap) {                                               \
            size_t nc = pow_cap ? pow_cap * 2 : 64;                            \
            PowItem *ns = realloc(pow_stack, nc * sizeof *ns);                 \
            if (!ns) {                                                         \
                fprintf(stderr, "calc: out of memory\n");                      \
                exit(1);                                                       \
            }                                                                  \
            pow_stack = ns;                                                    \
            pow_cap = nc;                                                      \
        }                                                                      \
        pow_stack[pow_sp].v = tmp_;                                            \
        pow_stack[pow_sp].start = st_;                                         \
        pow_stack[pow_sp].op = (OPPOS);                                        \
        pow_sp++;                                                              \
    } while (0)
    PUSH_OPERAND(0);
    while (P->tok.type == T_POW) {
        size_t op_pos = P->tok.pos;
        advance(P);
        PUSH_OPERAND(op_pos);
    }
#undef PUSH_OPERAND
    Value acc = pow_stack[pow_sp - 1].v;
    while (pow_sp - 1 > base) {
        PowItem *rhs = &pow_stack[pow_sp - 1];
        PowItem *lhs = &pow_stack[pow_sp - 2];
        if (apply(P, T_POW, lhs->v, acc, rhs->op, rhs->start, &acc) != 0) {
            pow_sp = base;
            return -1;
        }
        pow_sp--;
    }
    pow_sp = base;
    *out = acc;
    return 0;
}
static int parse_term(Parser *P, Value *out) {
    Value acc;
    if (power(P, &acc) != 0) return -1;
    while (P->tok.type == T_MUL || P->tok.type == T_DIV) {
        TokType op = P->tok.type;
        size_t op_pos = P->tok.pos;
        advance(P);
        size_t rhs_pos = P->tok.pos;
        Value rhs;
        if (power(P, &rhs) != 0) return -1;
        if (apply(P, op, acc, rhs, op_pos, rhs_pos, &acc) != 0) return -1;
    }
    *out = acc;
    return 0;
}
static int parse_expr(Parser *P, Value *out){
    Value acc;
    if (parse_term(P, &acc) != 0) return -1;
    while (P->tok.type == T_PLUS || P->tok.type == T_MINUS) {
        TokType op = P->tok.type;
        size_t op_pos = P->tok.pos;
        advance(P);
        size_t rhs_pos = P->tok.pos;
        Value rhs;
        if (parse_term(P, &rhs) != 0) return -1;
        if (apply(P, op, acc, rhs, op_pos, rhs_pos, &acc) != 0) return -1;
    }
    *out = acc;
    return 0;
}
static int parse_line(Parser *P, size_t start, size_t end, Value *out){
    P->cur = start;
    P->line_end = end;
    P->depth = 0;
    advance(P);
    if (parse_expr(P, out) != 0) return -1;
    if (P->tok.type != T_EOL) return fail(P, P->tok.pos);
    return 0;
}
typedef struct {
    char *buf;
    size_t len, cap;
} Out;
static void out_append(Out *o, const char *s, size_t n) {
    if (o->len + n + 1 > o->cap) {
        size_t cap = o->cap ? o->cap : 4096;
        while (o->len + n + 1 > cap) cap *= 2;
        char *nb = realloc(o->buf, cap);
        if (!nb) {
            fprintf(stderr, "calc: out of memory\n");
            exit(1);
        }
        o->buf = nb;
        o->cap = cap;
    }
    memcpy(o->buf + o->len, s, n);
    o->len += n;
}
// Evaluate the whole file held in src[0..len) and fill 'o' with the content
// of the result file.
static void evaluate(const char *src, size_t len, Out *o) {
    Parser P;
    memset(&P, 0, sizeof P);
    P.src = src;
    size_t pos = 0;
    while (pos < len) {
        const char *nl = memchr(src + pos, '\n', len - pos);
        size_t line_end = nl ? (size_t)(nl - src) : len;
        size_t k = pos;
        while (k < line_end && (src[k] == ' ' || src[k] == '\t')) k++;
        if (k < line_end && src[k] != '#') {
            Value v;
            if (parse_line(&P, pos, line_end, &v) != 0) {
                o->len = 0;
                char msg[64];
                int n = snprintf(msg, sizeof msg, "ERROR:%zu\n", P.err_pos + 1);
                out_append(o, msg, (size_t)n);
                break;
            }
            char num[64];
            int n;
            if (v.is_float) n = snprintf(num, sizeof num, "%.15g\n", v.d);
            else n = snprintf(num, sizeof num, "%lld\n", v.i);
            out_append(o, num, (size_t)n);
        }
        pos = line_end + 1;
    }
    free(P.scratch);
}
static int read_file(const char *path, char **data, size_t *len) {
    struct stat st;
    if (stat(path, &st) != 0) {
        fprintf(stderr, "calc: cannot open '%s': %s\n", path, strerror(errno));
        return -1;
    }
    if (!S_ISREG(st.st_mode)) {
        fprintf(stderr, "calc: '%s' is not a regular file\n", path);
        return -1;
    }
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "calc: cannot open '%s': %s\n", path, strerror(errno));
        return -1;
    }
    size_t cap = (size_t)st.st_size + 1, n = 0;
    char *buf = malloc(cap);
    if (!buf) {
        fprintf(stderr, "calc: out of memory\n");
        fclose(f);
        return -1;
    }
    for (;;) {
        size_t got = fread(buf + n, 1, cap - n, f);
        n += got;
        if (n < cap) break; // short read: end of file or error
        cap *= 2;
        char *nb = realloc(buf, cap);
        if (!nb) {
            fprintf(stderr, "calc: out of memory\n");
            free(buf);
            fclose(f);
            return -1;
        }
        buf = nb;
    }
    int bad = ferror(f);
    fclose(f);
    if (bad) {
        fprintf(stderr, "calc: error reading '%s'\n", path);
        free(buf);
        return -1;
    }
    *data = buf;
    *len = n;
    return 0;
}
// Create the output folder if needed (its parent is assumed to exist).
static int ensure_dir(const char *path) {
    if (mkdir(path, 0777) == 0) return 0;
    struct stat st;
    if (errno == EEXIST && stat(path, &st) == 0 && S_ISDIR(st.st_mode)) return 0;
    fprintf(stderr, "calc: cannot create output folder '%s': %s\n", path, strerror(errno));
    return -1;
}
// Last path component without trailing slashes, copied into a new string.
static char *base_name(const char *path) {
    size_t n = strlen(path);
    while (n > 1 && path[n - 1] == '/') n--;
    size_t start = n;
    while (start > 0 && path[start - 1] != '/') start--;
    char *r = malloc(n - start + 1);
    if (!r) return NULL;
    memcpy(r, path + start, n - start);
    r[n - start] = '\0';
    return r;
}
static int has_txt_ext(const char *name) {
    size_t n = strlen(name);
    return n > 4 && strcmp(name + n - 4, ".txt") == 0;
}
// Evaluate input_path and write <outdir>/<base>_<name>_<lastname>_<id>.txt.
static int process_file(const char *input_path, const char *outdir) {
    char *data = NULL;
    size_t len = 0;
    if (read_file(input_path, &data, &len) != 0) {
        return -1;
    }
    char *base = base_name(input_path);
    if (!base){
        free(data);
        fprintf(stderr, "calc: out of memory\n");
        return -1;
    }
    if (has_txt_ext(base)){
        base[strlen(base) - 4] = '\0';
    }
    Out o = {NULL, 0, 0};
    evaluate(data, len, &o);
    free(data);
    size_t plen = strlen(outdir) + strlen(base) + 64 + sizeof STUDENT_NAME + sizeof STUDENT_LASTNAME + sizeof STUDENT_ID;
    char *path = malloc(plen);
    int rc = -1;
    if (path) {
        snprintf(path, plen, "%s/%s_%s_%s_%s.txt", outdir, base,
                 STUDENT_NAME, STUDENT_LASTNAME, STUDENT_ID);
        FILE *f = fopen(path, "wb");
        if (!f) {
            fprintf(stderr, "calc: cannot write '%s': %s\n", path, strerror(errno));
        } else {
            size_t w = o.len ? fwrite(o.buf, 1, o.len, f) : 0;
            // fclose can fail on buffered data (disk full), so check it too.
            if (w != o.len || fclose(f) != 0){
                fprintf(stderr, "calc: error writing '%s'\n", path);
            } else{
                rc = 0;
            }
        }
    } else {
        fprintf(stderr, "calc: out of memory\n");
    }
    free(path);
    free(o.buf);
    free(base);
    return rc;
}
static void usage(void) {
    fprintf(stderr,"usage: calc [-d DIR | --dir DIR] [-o OUTDIR | --output-dir OUTDIR] [input.txt]\n");
}
int main(int argc, char **argv) {
    const char *dir = NULL, *outdir = NULL, *input = NULL;
    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        if (strcmp(a, "-d") == 0 || strcmp(a, "--dir") == 0) {
            if (i + 1 >= argc) { fprintf(stderr, "calc: option '%s' needs an argument\n", a); usage(); return 2; }
            dir = argv[++i];
        } else if (strcmp(a, "-o") == 0 || strcmp(a, "--output-dir") == 0) {
            if (i + 1 >= argc) { fprintf(stderr, "calc: option '%s' needs an argument\n", a); usage(); return 2; }
            outdir = argv[++i];
        } else if (a[0] == '-' && a[1] != '\0') {
            fprintf(stderr, "calc: unknown option '%s'\n", a);
            usage();
            return 2;
        } else if (input){
            fprintf(stderr, "calc: more than one input file given\n");
            usage();
            return 2;
        } else {
            input = a;
        }
    }
    if (!dir && !input) { 
        usage(); return 2;
    }
    if (dir && input){
        fprintf(stderr, "calc: give either an input file or -d DIR, not both\n");
        usage();
        return 2;
    }
    int rc = 0;
    char *default_out = NULL;
    char *base = base_name(dir ? dir : input);
    if (!base) { 
        fprintf(stderr, "calc: out of memory\n"); return 1; 
    }
    DIR *d = NULL;
    if (dir) {
        d = opendir(dir);
        if (!d) {
            fprintf(stderr, "calc: cannot open folder '%s': %s\n", dir, strerror(errno));
            free(base);
            return 1;
        }
    } else {
        struct stat st;
        if (stat(input, &st) != 0) {
            fprintf(stderr, "calc: cannot open '%s': %s\n", input, strerror(errno));
            free(base);
            return 1;
        }
        if (!S_ISREG(st.st_mode)) {
            fprintf(stderr, "calc: '%s' is not a regular file\n", input);
            free(base);
            return 1;
        }
    }
    if (!outdir) {
        if (!dir && has_txt_ext(base)) base[strlen(base) - 4] = '\0';
        size_t n = strlen(base) + sizeof STUDENT_NAME + sizeof STUDENT_ID + 4;
        default_out = malloc(n);
        if (!default_out) {
            fprintf(stderr, "calc: out of memory\n");
            if (d) closedir(d);
            free(base);
            return 1;
        }
        snprintf(default_out, n, "%s_%s_%s", base, STUDENT_NAME, STUDENT_ID);
        outdir = default_out;
    }
    if (ensure_dir(outdir) != 0) {
        rc = 1;
    } else if (!dir) {
        if (process_file(input, outdir) != 0) rc = 1;
    } else{
        struct dirent *e;
        while ((e = readdir(d)) != NULL) {
            if (!has_txt_ext(e->d_name)){
                continue;
            }
            size_t n = strlen(dir) + strlen(e->d_name) + 2;
            char *p = malloc(n);
            if (!p) {
                fprintf(stderr, "calc: out of memory\n"); rc = 1; break; 
            }
            snprintf(p, n, "%s/%s", dir, e->d_name);
            struct stat st;
            if (stat(p, &st) == 0 && S_ISREG(st.st_mode)){
                if (process_file(p, outdir) != 0){
                    rc = 1;
                }
            }
            free(p);
        }
    }
    if (d) closedir(d);
    free(default_out);
    free(base);
    free(pow_stack);
    return rc;
}