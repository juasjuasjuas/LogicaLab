%{
/* tarea1.lex - Deduccion Natural | Logica Computacional 22625 */
/* Compilar: flex tarea1.lex && gcc -o tarea1.exe lex.yy.c -lfl */
/* Ejecutar: ./tarea1.exe < expresion.txt                        */
#include <stdio.h>
#include <stdlib.h>

/* ------------------------------------------------------------------ */
/* Constantes                                                          */
/* ------------------------------------------------------------------ */
#define MAX   64
#define FMAX  256
#define NMAX  32

/* Tipos de token */
#define TOK_VAR    0
#define TOK_NEG    1
#define TOK_AND    2
#define TOK_IMP    3
#define TOK_VDASH  4
#define TOK_LPAREN 5
#define TOK_RPAREN 6
#define TOK_COMMA  7

/* Prefijo canonico de cada tipo de nodo en la formula */
#define CNEG '0'
#define CAND '1'
#define CIMP '2'

/* ------------------------------------------------------------------ */
/* Variables globales                                                  */
/* ------------------------------------------------------------------ */
int  tokens[MAX];        /* tipos de token del sequent actual         */
char tokvar[MAX][NMAX];  /* nombre de variable cuando token es VAR    */
int  ntokens;            /* cantidad de tokens recolectados            */
int  pos;                /* cursor del parser sobre tokens[]           */

char tab[MAX][FMAX];     /* tabla: formula en notacion canonica        */
char jus[MAX][FMAX];     /* tabla: justificacion de cada linea         */
int  niv[MAX];           /* tabla: nivel de anidamiento                */
int  ntab;               /* cantidad de lineas en la tabla             */

int  dentro;             /* 1 si estamos dentro de $$ ... $$           */

/* ------------------------------------------------------------------ */
/* Operaciones sobre strings (sin usar libreria)                       */
/* ------------------------------------------------------------------ */

/* Retorna 1 si a y b son iguales caracter a caracter */
int sequ(char *a, char *b) {
   int i;
   i = 0;
   while (a[i] && b[i] && a[i] == b[i]) i = i + 1;
   return a[i] == b[i];
}

/* Copia src en dst */
void scopy(char *dst, char *src) {
   int i;
   i = 0;
   while (src[i]) { dst[i] = src[i]; i = i + 1; }
   dst[i] = '\0';
}

/* ------------------------------------------------------------------ */
/* Construccion de formulas canonicas                                  */
/* Formato: CNEG(A) para negacion, CAND(A,B) o CIMP(A,B) para binarios*/
/* ------------------------------------------------------------------ */

/* Construye "0(a)" en out */
void make_neg(char *out, char *a) {
   int i, j;
   i = 0; j = 0;
   out[i] = CNEG; i = i + 1;
   out[i] = '(';  i = i + 1;
   while (a[j]) { out[i] = a[j]; i = i + 1; j = j + 1; }
   out[i] = ')';  i = i + 1;
   out[i] = '\0';
}

/* Construye "op(a,b)" en out para operadores binarios */
void make_bin(char *out, char op, char *a, char *b) {
   int i, j;
   i = 0; j = 0;
   out[i] = op;  i = i + 1;
   out[i] = '('; i = i + 1;
   while (a[j]) { out[i] = a[j]; i = i + 1; j = j + 1; }
   out[i] = ','; i = i + 1;
   j = 0;
   while (b[j]) { out[i] = b[j]; i = i + 1; j = j + 1; }
   out[i] = ')'; i = i + 1;
   out[i] = '\0';
}

/* Extrae subformula de "op(...)" en out:
   which=0 retorna el primer argumento  (izquierdo o interior)
   which=1 retorna el segundo argumento (solo para binarios)
   Cuenta profundidad de parentesis para manejar formulas anidadas   */
void get_sub(char *out, char *f, int which) {
   int i, j, depth, found;
   i = 2; j = 0; depth = 0; found = 0;
   while (f[i] && !(f[i] == ')' && depth == 0)) {
      if (f[i] == ',' && depth == 0) {
         found = 1;
         i = i + 1;
      } else {
         if (f[i] == '(') depth = depth + 1;
         if (f[i] == ')') depth = depth - 1;
         if (which == 0 && found == 0) {
            out[j] = f[i];
            j = j + 1;
         } else if (which == 1 && found == 1) {
            out[j] = f[i];
            j = j + 1;
         }
         i = i + 1;
      }
   }
   out[j] = '\0';
}

/* ------------------------------------------------------------------ */
/* Tabla de demostracion                                               */
/* ------------------------------------------------------------------ */

/* Agrega una linea a la tabla, retorna numero de linea base 1 */
int agrega(char *f, char *j, int nivel) {
   int i;
   if (ntab > MAX - 1) return -1;
   i = 0;
   while (f[i] && i < FMAX - 1) { tab[ntab][i] = f[i]; i = i + 1; }
   tab[ntab][i] = '\0';
   i = 0;
   while (j[i] && i < FMAX - 1) { jus[ntab][i] = j[i]; i = i + 1; }
   jus[ntab][i] = '\0';
   niv[ntab] = nivel;
   ntab = ntab + 1;
   return ntab;
}

/* Busca f en tabla hasta linea lim, retorna nro linea o -1 */
int busca(char *f, int lim) {
   int i;
   i = 0;
   while (i < lim && i < ntab) {
      if (sequ(tab[i], f)) return i + 1;
      i = i + 1;
   }
   return -1;
}

/* Construye justificacion "pre + nroA + sep + nroB + suf" en out    */
void build_jus(char *out, char *pre, int a, char *sep, int b, char *suf) {
   char na[8], nb[8];
   int i, k, n;
   k = 0;
   i = 0;
   while (pre[i] && k < FMAX - 1) { out[k] = pre[i]; k = k + 1; i = i + 1; }
   if (a > 0) {
      n = a; i = 0;
      while (n > 0) { na[i] = '0' + (n % 10); i = i + 1; n = n / 10; }
      n = i;
      while (n > 0) { n = n - 1; out[k] = na[n]; k = k + 1; }
   }
   if (sep) {
      i = 0;
      while (sep[i] && k < FMAX - 1) { out[k] = sep[i]; k = k + 1; i = i + 1; }
   }
   if (b > 0) {
      n = b; i = 0;
      while (n > 0) { nb[i] = '0' + (n % 10); i = i + 1; n = n / 10; }
      n = i;
      while (n > 0) { n = n - 1; out[k] = nb[n]; k = k + 1; }
   }
   if (suf) {
      i = 0;
      while (suf[i] && k < FMAX - 1) { out[k] = suf[i]; k = k + 1; i = i + 1; }
   }
   out[k] = '\0';
}

/* ------------------------------------------------------------------ */
/* Impresion de formula canonica en LaTeX                              */
/* ------------------------------------------------------------------ */
void pflat(char *f) {
   char l[FMAX], r[FMAX];
   if (!f || !f[0]) return;
   if (f[0] == CNEG) {
      get_sub(l, f, 0);
      printf("\\neg ");
      if (l[0] == CIMP || l[0] == CAND) {
         printf("("); pflat(l); printf(")");
      } else {
         pflat(l);
      }
      return;
   }
   if (f[0] == CAND || f[0] == CIMP) {
      get_sub(l, f, 0);
      get_sub(r, f, 1);
      if (l[0] == CIMP) { printf("("); pflat(l); printf(")"); }
      else pflat(l);
      if (f[0] == CAND) printf(" \\wedge ");
      else              printf(" \\rightarrow ");
      if (r[0] == CIMP) { printf("("); pflat(r); printf(")"); }
      else pflat(r);
      return;
   }
   printf("\\mbox{\\bf %s}", f);
}

/* ------------------------------------------------------------------ */
/* Impresion de la tabla completa en LaTeX                             */
/* ------------------------------------------------------------------ */
void imprime(void) {
   int i;
   char *col;
   printf("{\\tiny\n\\begin{tabular}{r l l}\n");
   i = 0;
   while (i < ntab) {
      if (niv[i] == 1)      col = "green";
      else if (niv[i] == 2) col = "red";
      else                  col = "blue";
      if (niv[i] == 0 && jus[i][0] == 'P') {
         printf("%d & $", i + 1);
         pflat(tab[i]);
         printf("$ & %s \\\\ \\\\\n", jus[i]);
      } else {
         printf("{\\color{%s} %d} & {\\color{%s} $", col, i + 1, col);
         pflat(tab[i]);
         printf("$} & {\\color{%s} %s} \\\\ \\\\\n", col, jus[i]);
      }
      i = i + 1;
   }
   printf("\\end{tabular}\n}\n\n");
}

/* ------------------------------------------------------------------ */
/* Parser recursivo descendente                                        */
/* Lee tokens[pos..] y escribe formula canonica en out                */
/* La cadena de llamadas determina la precedencia:                    */
/*   formula -> implication -> conjunction -> negation -> atom        */
/* Lo mas profundo liga mas fuerte (negation liga mas que conjunction)*/
/* ------------------------------------------------------------------ */
void parse_formula(char *out);

void parse_atom(char *out) {
   char inner[FMAX];
   if (pos < ntokens && tokens[pos] == TOK_LPAREN) {
      pos = pos + 1;
      parse_formula(inner);
      if (pos < ntokens && tokens[pos] == TOK_RPAREN) pos = pos + 1;
      scopy(out, inner);
   } else if (pos < ntokens && tokens[pos] == TOK_VAR) {
      scopy(out, tokvar[pos]);
      pos = pos + 1;
   } else {
      out[0] = '\0';
   }
}

void parse_negation(char *out) {
   char inner[FMAX];
   if (pos < ntokens && tokens[pos] == TOK_NEG) {
      pos = pos + 1;
      parse_negation(inner);
      make_neg(out, inner);
   } else {
      parse_atom(out);
   }
}

void parse_conjunction(char *out) {
   char left[FMAX], right[FMAX];
   parse_negation(left);
   while (pos < ntokens && tokens[pos] == TOK_AND) {
      pos = pos + 1;
      parse_negation(right);
      make_bin(out, CAND, left, right);
      scopy(left, out);
   }
   scopy(out, left);
}

void parse_implication(char *out) {
   char left[FMAX], right[FMAX];
   parse_conjunction(left);
   if (pos < ntokens && tokens[pos] == TOK_IMP) {
      pos = pos + 1;
      parse_implication(right);
      make_bin(out, CIMP, left, right);
   } else {
      scopy(out, left);
   }
}

void parse_formula(char *out) {
   parse_implication(out);
}

/* ------------------------------------------------------------------ */
/* Motor de deduccion natural (backward chaining)                     */
/* prof limita profundidad de recursion mutua entre elimina/demuestra */
/* ------------------------------------------------------------------ */

/* ------------------------------------------------------------------ */
/* FIX 1 - Pruebas 16, 25                                             */
/* Expande todas las conjunciones de la tabla extrayendo sus partes   */
/* de forma iterativa hasta que no haya nada nuevo que agregar.       */
/* Hereda el nivel de la conjuncion de origen para colorear correcto. */
/* ------------------------------------------------------------------ */
void extrae_and(void) {
   char ant[FMAX], con[FMAX], jbuf[FMAX];
   int i, cambio, lim;
   cambio = 1;
   while (cambio == 1) {
      cambio = 0;
      lim = ntab;
      i = 0;
      while (i < lim) {
         if (tab[i][0] == CAND) {
            get_sub(ant, tab[i], 0);
            get_sub(con, tab[i], 1);
            if (busca(ant, ntab) < 0) {
               build_jus(jbuf, "$\\wedge_{e1} ~~ ", i + 1, NULL, 0, "$");
               agrega(ant, jbuf, niv[i]);
               cambio = 1;
            }
            if (busca(con, ntab) < 0) {
               build_jus(jbuf, "$\\wedge_{e2} ~~ ", i + 1, NULL, 0, "$");
               agrega(con, jbuf, niv[i]);
               cambio = 1;
            }
         }
         i = i + 1;
      }
   }
}

/* ------------------------------------------------------------------ */
/* FIX 7 - Prueba 38                                                  */
/* Propaga ~~e en cadena: si ~~A esta en tabla y A no, agrega A.      */
/* Itera hasta saturar, permitiendo desanidar negaciones multiples    */
/* (4, 5, 6... niveles) sin depender de recursion en elimina().       */
/* ------------------------------------------------------------------ */
void extrae_neg(void) {
   char inner[FMAX], sub[FMAX], jbuf[FMAX];
   int i, cambio, lim;
   cambio = 1;
   while (cambio == 1) {
      cambio = 0;
      lim = ntab;
      i = 0;
      while (i < lim) {
         if (tab[i][0] == CNEG) {
            get_sub(inner, tab[i], 0);
            if (inner[0] == CNEG) {
               get_sub(sub, inner, 0);
               if (busca(sub, ntab) < 0) {
                  build_jus(jbuf, "${\\neg \\neg}_e ~~ ", i + 1,
                            NULL, 0, "$");
                  agrega(sub, jbuf, niv[i]);
                  cambio = 1;
               }
            }
         }
         i = i + 1;
      }
   }
}

/* ------------------------------------------------------------------ */
/* FIX 8 - Prueba 68                                                  */
/* Construye conjunciones A^B cuando A y B estan en tabla Y A^B es   */
/* antecedente de alguna implicacion presente. Evita generar todas    */
/* las combinaciones posibles; solo las utiles para ->_e.             */
/* ------------------------------------------------------------------ */
void forward_and(int nivel) {
   char ant[FMAX], la[FMAX], lb[FMAX], jbuf[FMAX];
   int i, cambio, lim, ra, rb;
   cambio = 1;
   while (cambio == 1) {
      cambio = 0;
      lim = ntab;
      i = 0;
      while (i < lim) {
         if (tab[i][0] == CIMP) {
            get_sub(ant, tab[i], 0);
            if (ant[0] == CAND) {
               get_sub(la, ant, 0);
               get_sub(lb, ant, 1);
               ra = busca(la, ntab);
               rb = busca(lb, ntab);
               if (ra > 0 && rb > 0 && busca(ant, ntab) < 0) {
                  build_jus(jbuf, "$\\wedge_i ~~ ", ra, ", ", rb, "$");
                  agrega(ant, jbuf, nivel);
                  cambio = 1;
               }
            }
         }
         i = i + 1;
      }
   }
}

/* ------------------------------------------------------------------ */
/* FIX 2 - Prueba 27                                                  */
/* Detecta si existe algun par A / ~A en la tabla hasta lim.          */
/* Retorna 1 si hay contradiccion, 0 si no.                           */
/* ------------------------------------------------------------------ */
int hay_contradiccion(int lim) {
   char neg[FMAX];
   int i;
   i = 0;
   while (i < lim) {
      make_neg(neg, tab[i]);
      if (busca(neg, lim) > 0) return 1;
      i = i + 1;
   }
   return 0;
}

/* ------------------------------------------------------------------ */
/* FIX 3 - Prueba 32                                                  */
/* Aplica modus ponens hacia adelante (forward chaining) sobre        */
/* implicaciones cuyo antecedente ya esta en tabla. Itera hasta       */
/* saturar, evitando ciclos al verificar con busca() antes de agregar.*/
/* ------------------------------------------------------------------ */
void forward_imp(int nivel) {
   char ant[FMAX], con[FMAX], jbuf[FMAX];
   int i, cambio, lim, ra, ri;
   cambio = 1;
   while (cambio == 1) {
      cambio = 0;
      lim = ntab;
      i = 0;
      while (i < lim) {
         if (tab[i][0] == CIMP) {
            get_sub(ant, tab[i], 0);
            get_sub(con, tab[i], 1);
            ra = busca(ant, ntab);
            if (ra > 0 && busca(con, ntab) < 0) {
               ri = i + 1;
               build_jus(jbuf, "$\\rightarrow_e ~~ ", ri, ", ", ra, "$");
               agrega(con, jbuf, nivel);
               cambio = 1;
            }
         }
         i = i + 1;
      }
   }
}

/* ------------------------------------------------------------------ */
/* FIX 9 - Pruebas 41, 67                                             */
/* Aplica modus tollens hacia adelante: si A->B en tabla y ~B en      */
/* tabla, agrega ~A. Itera hasta saturar. Permite encadenar MT sin    */
/* depender del motor backward, resolviendo cadenas ~s->~r->~q->~p.  */
/* ------------------------------------------------------------------ */
void forward_mt(int nivel) {
   char ant[FMAX], con[FMAX], negcon[FMAX], negant[FMAX], jbuf[FMAX];
   int i, cambio, lim, rc, ri;
   cambio = 1;
   while (cambio == 1) {
      cambio = 0;
      lim = ntab;
      i = 0;
      while (i < lim) {
         if (tab[i][0] == CIMP) {
            get_sub(ant, tab[i], 0);
            get_sub(con, tab[i], 1);
            make_neg(negcon, con);
            make_neg(negant, ant);
            rc = busca(negcon, ntab);
            if (rc > 0 && busca(negant, ntab) < 0) {
               ri = i + 1;
               build_jus(jbuf, "MT ", ri, ", ", rc, NULL);
               agrega(negant, jbuf, nivel);
               cambio = 1;
            }
         }
         i = i + 1;
      }
   }
}

/* ------------------------------------------------------------------ */
/* FIX 4 - Pruebas 33, 34                                             */
/* Si existe ~(A->B) en tabla, agrega A y ~B usando la equivalencia   */
/* clasica ~(A->B) <=> A ^ ~B. Solo agrega lo que aun no esta.       */
/* ------------------------------------------------------------------ */
void expande_neg_imp(int nivel) {
   char inner[FMAX], ant[FMAX], con[FMAX], negcon[FMAX], jbuf[FMAX];
   int i, lim;
   lim = ntab;
   i = 0;
   while (i < lim) {
      if (tab[i][0] == CNEG) {
         get_sub(inner, tab[i], 0);
         if (inner[0] == CIMP) {
            get_sub(ant, inner, 0);
            get_sub(con, inner, 1);
            make_neg(negcon, con);
            if (busca(ant, ntab) < 0) {
               build_jus(jbuf, "$\\neg\\rightarrow_{e1} ~~ ",
                         i + 1, NULL, 0, "$");
               agrega(ant, jbuf, niv[i]);
            }
            if (busca(negcon, ntab) < 0) {
               build_jus(jbuf, "$\\neg\\rightarrow_{e2} ~~ ",
                         i + 1, NULL, 0, "$");
               agrega(negcon, jbuf, niv[i]);
            }
         }
      }
      i = i + 1;
   }
}

int demuestra(char *m, int nivel, int prof);

int elimina(char *m, int nivel, int prof) {
   char neg[FMAX], nn[FMAX];
   char ant[FMAX], con[FMAX];
   char ny[FMAX], nm[FMAX], nnm[FMAX];
   char jbuf[FMAX];
   int i, lim, r, ri, rd, sv;
   if (prof > 20) return -1;
   r = busca(m, ntab);
   if (r > 0) return r;

   /* ---------------------------------------------------------------- */
   /* Saturacion completa hasta punto fijo: cada funcion puede usar    */
   /* los resultados de las anteriores en la misma ronda, y el loop   */
   /* repite hasta que ninguna agrega nada nuevo.                      */
   /* ---------------------------------------------------------------- */
   {
      int ntab_antes, ntab_nuevo;
      ntab_antes = -1;
      ntab_nuevo = ntab;
      while (ntab_antes != ntab_nuevo) {
         ntab_antes = ntab_nuevo;
         extrae_and();
         extrae_neg();
         expande_neg_imp(nivel);
         forward_and(nivel);
         forward_imp(nivel);
         forward_mt(nivel);
         ntab_nuevo = ntab;
      }
   }

   /* re-verificar tras saturacion */
   r = busca(m, ntab);
   if (r > 0) return r;

   /* actualizar lim tras expansion (FIX 5 - Prueba 35) */
   lim = ntab;

   /* ---------------------------------------------------------------- */
   /* FIX 2: ex falso quodlibet - si hay contradiccion en tabla,      */
   /* cualquier formula es derivable (bottom elimination).             */
   /* ---------------------------------------------------------------- */
   if (hay_contradiccion(lim) > 0) {
      build_jus(jbuf, "$\\bot_e$", 0, NULL, 0, NULL);
      return agrega(m, jbuf, nivel);
   }

   /* neg-neg-e directa: si ~~m esta en tabla, eliminar doble negacion */
   make_neg(neg, m);
   make_neg(nn, neg);
   r = busca(nn, lim);
   if (r > 0) {
      build_jus(jbuf, "${\\neg \\neg}_e ~~ ", r, NULL, 0, "$");
      return agrega(m, jbuf, nivel);
   }

   /* ---------------------------------------------------------------- */
   /* ->_e modus ponens: buscar A->m en tabla hasta lim actualizado,  */
   /* luego intentar derivar A usando elimina() en lugar de           */
   /* demuestra() para aprovechar la tabla ya saturada (FIX 5).       */
   /* ---------------------------------------------------------------- */
   i = 0;
   while (i < lim) {
      if (tab[i][0] == CIMP) {
         get_sub(con, tab[i], 1);
         if (sequ(con, m)) {
            get_sub(ant, tab[i], 0);
            r = busca(ant, ntab);
            if (r < 0) r = elimina(ant, nivel, prof + 1);
            if (r > 0) {
               build_jus(jbuf, "$\\rightarrow_e ~~ ", i + 1, ", ", r, "$");
               return agrega(m, jbuf, nivel);
            }
         }
      }
      i = i + 1;
   }

   /* ---------------------------------------------------------------- */
   /* FIX 6 - Prueba 12                                               */
   /* neg-neg-i en elimina: si m=~~X y X esta en tabla, construir    */
   /* ~~X directamente. Necesario para que MT pueda usar ~~X como    */
   /* premisa negada al aplicar modus tollens sobre ~X->~Y.          */
   /* ---------------------------------------------------------------- */
   if (m[0] == CNEG) {
      get_sub(ant, m, 0);
      if (ant[0] == CNEG) {
         get_sub(con, ant, 0);
         r = busca(con, ntab);
         if (r > 0) {
            build_jus(jbuf, "${\\neg \\neg}_i ~~ ", r, NULL, 0, "$");
            return agrega(m, jbuf, nivel);
         }
      }
   }

   /* MT: si m=~X, buscar X->Y en tabla y demostrar ~Y               */
   if (m[0] == CNEG) {
      get_sub(ant, m, 0);
      i = 0;
      while (i < lim) {
         if (tab[i][0] == CIMP) {
            get_sub(con, tab[i], 0);
            if (sequ(con, ant)) {
               get_sub(con, tab[i], 1);
               make_neg(ny, con);
               r = busca(ny, ntab);
               if (r < 0) r = elimina(ny, nivel, prof + 1);
               if (r > 0) {
                  build_jus(jbuf, "MT ", i + 1, ", ", r, NULL);
                  return agrega(m, jbuf, nivel);
               }
            }
         }
         i = i + 1;
      }
   }

   /* neg-neg-e indirecta: intentar derivar ~~m y luego eliminar      */
   if (m[0] != CNEG) {
      make_neg(nm, m);
      make_neg(nnm, nm);
      r = busca(nnm, ntab);
      if (r < 0) r = elimina(nnm, nivel, prof + 1);
      if (r > 0) {
         build_jus(jbuf, "${\\neg \\neg}_e ~~ ", r, NULL, 0, "$");
         return agrega(m, jbuf, nivel);
      }
   }

   /* ^_i: si m=A^B, demostrar A y B por separado y combinar          */
   /* Nota: ^_e1 y ^_e2 ahora los maneja extrae_and() al inicio,      */
   /* por lo que este bloque solo cubre la introduccion.               */
   if (m[0] == CAND) {
      sv = ntab;
      get_sub(ant, m, 0);
      get_sub(con, m, 1);
      ri = busca(ant, ntab);
      if (ri < 0) ri = demuestra(ant, nivel, prof + 1);
      rd = busca(con, ntab);
      if (rd < 0) rd = demuestra(con, nivel, prof + 1);
      if (ri > 0 && rd > 0) {
         build_jus(jbuf, "$\\wedge_i ~~ ", ri, ", ", rd, "$");
         return agrega(m, jbuf, nivel);
      }
      ntab = sv;
   }

   return -1;
}

int demuestra(char *m, int nivel, int prof) {
   char ant[FMAX], con[FMAX];
   char inner[FMAX], negk[FMAX];
   char jbuf[FMAX];
   char ant2[FMAX], con2[FMAX], jbuf2[FMAX];
   int r, ra, ls, lb, sv, ls2, k, r2, sv2, ra2, rb2;
   if (prof > 20) return -1;
   ra = busca(m, ntab);
   if (ra > 0) return ra;
   if (elimina(m, nivel, prof + 1) > 0) return ntab;
   /* ->_i: suponer antecedente y demostrar consecuente               */
   if (m[0] == CIMP) {
      sv = ntab;
      get_sub(ant, m, 0);
      get_sub(con, m, 1);
      ls = agrega(ant, "Supuesto", nivel + 1);
      lb = demuestra(con, nivel + 1, prof + 1);
      if (lb < 0) { ntab = sv; return -1; }
      build_jus(jbuf, "$\\rightarrow_i ~~ ", ls, "-", lb, "$");
      return agrega(m, jbuf, nivel);
   }
   /* neg-neg-i: si m=~~A, demostrar A                                */
   if (m[0] == CNEG) {
      get_sub(inner, m, 0);
      if (inner[0] == CNEG) {
         get_sub(ant, inner, 0);
         ra = busca(ant, ntab);
         if (ra < 0) ra = demuestra(ant, nivel, prof + 1);
         if (ra > 0) {
            build_jus(jbuf, "${\\neg \\neg}_i ~~ ", ra, NULL, 0, "$");
            return agrega(m, jbuf, nivel);
         }
      }
   }
   /* neg-i: suponer ant(m), buscar contradiccion B y ~B              */
   if (m[0] == CNEG) {
      sv = ntab;
      get_sub(ant, m, 0);
      ls2 = agrega(ant, "Supuesto", nivel + 1);
      /* ------------------------------------------------------------ */
      /* FIX 8 - Prueba 68                                            */
      /* Con el supuesto recien agregado, intentar construir           */
      /* conjunciones A^B que esten en tabla como implicante          */
      /* (ej: p^q->r con p premisa y q supuesto). Saturar antes       */
      /* de buscar contradiccion permite que forward_imp encuentre r. */
      /* ------------------------------------------------------------ */
      /* saturacion completa con supuesto recien agregado */
      {
         int ntab_antes, ntab_nuevo;
         ntab_antes = -1;
         ntab_nuevo = ntab;
         while (ntab_antes != ntab_nuevo) {
            ntab_antes = ntab_nuevo;
            extrae_and();
            extrae_neg();
            expande_neg_imp(nivel + 1);
            forward_and(nivel + 1);
            forward_imp(nivel + 1);
            forward_mt(nivel + 1);
            ntab_nuevo = ntab;
         }
      }
      k = 0; r2 = -1;
      while (k < ls2 && r2 < 0) {
         make_neg(negk, tab[k]);
         sv2 = ntab;
         r2 = elimina(negk, nivel + 1, prof + 1);
         if (r2 < 0) { ntab = sv2; k = k + 1; }
      }
      if (r2 > 0) {
         build_jus(jbuf, "$\\neg_i ~~ ", ls2, "-", r2, "$");
         return agrega(m, jbuf, nivel);
      }
      ntab = sv;
   }
   return -1;
}

/* ------------------------------------------------------------------ */
/* Procesa el sequent recolectado en tokens[]                         */
/* ------------------------------------------------------------------ */
void procesa(void) {
   char prem[MAX][FMAX];
   char conc[FMAX];
   int nprem, vdash, i, r;
   vdash = -1; i = 0;
   while (i < ntokens) {
      if (tokens[i] == TOK_VDASH) vdash = i;
      i = i + 1;
   }
   nprem = 0;
   pos = 0;
   if (vdash > 0) {
      while (pos < vdash) {
         parse_formula(prem[nprem]);
         if (prem[nprem][0]) nprem = nprem + 1;
         if (pos < vdash && tokens[pos] == TOK_COMMA) pos = pos + 1;
      }
   }
   if (vdash > -1) pos = vdash + 1;
   else            pos = 0;
   parse_formula(conc);
   ntab = 0;
   i = 0;
   while (i < nprem) {
      agrega(prem[i], "Premisa", 0);
      i = i + 1;
   }
   r = demuestra(conc, 0, 0);
   if (r < 0) printf("%% No se pudo demostrar.\n");
   else       imprime();
}

%}

letra    [a-zA-Z]
variable {letra}+
esp      [ \t\n\r]+
neg      \\neg
conj     \\wedge
impl     \\rightarrow
vdash    \\vdash
mbox     \\mbox\{\\bf[ \t]*{variable}[ \t]*\}
delim    \$\$

%%

{delim} {
   if (dentro == 0) {
      dentro = 1;
      ntokens = 0;
   } else {
      dentro = 0;
      procesa();
   }
}

{mbox} {
   int ii, jj;
   if (dentro == 1) {
      ii = 0;
      while (yytext[ii] && yytext[ii] != 'f') ii = ii + 1;
      ii = ii + 1;
      while (yytext[ii] == ' ' || yytext[ii] == '\t') ii = ii + 1;
      jj = 0;
      while (yytext[ii] && yytext[ii] != '}' && jj < NMAX - 1) {
         tokvar[ntokens][jj] = yytext[ii];
         ii = ii + 1;
         jj = jj + 1;
      }
      while (jj > 0 && tokvar[ntokens][jj - 1] == ' ') jj = jj - 1;
      tokvar[ntokens][jj] = '\0';
      tokens[ntokens] = TOK_VAR;
      ntokens = ntokens + 1;
   }
}

{neg}   { if (dentro == 1) { tokens[ntokens] = TOK_NEG;    ntokens = ntokens + 1; } }
{conj}  { if (dentro == 1) { tokens[ntokens] = TOK_AND;    ntokens = ntokens + 1; } }
{impl}  { if (dentro == 1) { tokens[ntokens] = TOK_IMP;    ntokens = ntokens + 1; } }
{vdash} { if (dentro == 1) { tokens[ntokens] = TOK_VDASH;  ntokens = ntokens + 1; } }
"("     { if (dentro == 1) { tokens[ntokens] = TOK_LPAREN; ntokens = ntokens + 1; } }
")"     { if (dentro == 1) { tokens[ntokens] = TOK_RPAREN; ntokens = ntokens + 1; } }
","     { if (dentro == 1) { tokens[ntokens] = TOK_COMMA;  ntokens = ntokens + 1; } }

{esp} { }
.     { }

%%

int main(void) {
   dentro = 0;
   ntokens = 0;
   ntab = 0;
   yylex();
   return 0;
}
