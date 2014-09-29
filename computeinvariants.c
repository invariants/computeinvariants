/*
 ============================================================================
 Name        : computeinvariants.c
 Author      : Benjamin Otto
 Version     : 1.0
 Description : Berechne Invarianten von Dimension 6 Codes im F_2^12
 ============================================================================

The MIT License (MIT)

Copyright (c) 2014 Benjamin Otto.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#define NDEBUG
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>
#include "uthash.h" // http://troydhanson.github.io/uthash/userguide.html
#include "lookup.h"

#define NUM_CODEWORDS 64
#define DIM 12
#define DIMDIM 144
#define THREEDIMMINUS3 33
#define RANK 6
#define NUM_PREFIX 6
#define NUM_VECTORS_WITH_PREFIX 64
#define NUM_WEIGHTS_BASIC 8
#define NUM_MAX_COMBS 1716
#define NUM_MAX_VECTORS 4096
#define ANZ_CODES 1277642344
#define NUM_KOEFF_HAMMING 13
#define NUM_KOEFF_DOUBLE 25
#define NUM_KOEFF_TRIPLE 37
#define KEY_BUFF_SIZE 457 // Anzahl max Chars, um die ersten beiden Polys als String darzustellen
#define KEY_BUFF_SIZE_ALL 901

unsigned int g_vectors[RANK][NUM_VECTORS_WITH_PREFIX];

typedef struct list_node {
	unsigned int vector;
	struct list_node* next;
} list_node;

typedef struct codes {
	int generator1;
	int generator2;
	int generator3;
	int generator4;
	int generator5;
	int generator6;
	int hamming_weight[NUM_KOEFF_TRIPLE];
	int doube_weight[NUM_KOEFF_TRIPLE];
	int triple_weight[NUM_KOEFF_TRIPLE];
	char invariants_key[KEY_BUFF_SIZE];
	UT_hash_handle hh; /* structur hashable machen */
} codes;

codes* codes_invarianten = NULL;

typedef struct codes_known {
	char invariants_key_all[KEY_BUFF_SIZE_ALL];
	UT_hash_handle hh; /* structur hashable machen */
} codes_known;

codes_known* codes_known_sigs = NULL;

FILE *invariants_txt;
FILE *erfolg;

#define for_each_item_next(item, list) \
    for(list_node * item = list->next; item != NULL; item = item->next)

void showbits(unsigned int x) {
	for (int i = 11; i >= 0; i--) {
		if ((x & (1 << i))) {
			putchar('1');
		} else {
			putchar('0');
		}
		if (((i % 3) == 0) && (i != 0) && (i != 15)) {
			putchar(' ');
		}
	}
}

void showbits_file(unsigned int x) {
	for (int i = 11; i >= 0; i--) {
		if ((x & (1 << i))) {
			fputc('1', erfolg);
		} else {
			fputc('0', erfolg);
		}
	}
}

// Schnellster popcount fuer 32 Bit ints, deren ersten 20 Bits nicht gesetzt sind
static int popcount12(uint32_t word) {
	return (wordbits[word]); // lookup.h: static uint8_t wordbits[4096]
}

// Triple Poly aus den Codewoertern generieren,
// optimiert auf Symmetrie
void gen_triple_weight_polynomial(unsigned int all_codes[],
		int triple_weight_polynomial[]) {
	for (int i = 0; i < NUM_CODEWORDS; i++) {
		for (int j = i + 1; j < NUM_CODEWORDS; j++) {
			for (int k = j + 1; k < NUM_CODEWORDS; k++) {
				int weight_i = popcount12(all_codes[i]);
				int weight_j = popcount12(all_codes[j]);
				int weight_k = popcount12(all_codes[k]);
				// Trick: <c1, c2, c3> = wt( c1 BIT_AND c2 BIT_AND c3 )
				int koeff =
				DIMDIM * popcount12(all_codes[i] & all_codes[j] & all_codes[k]) - DIM * ((weight_i * popcount12(
						all_codes[j] & all_codes[k]) + (weight_j * popcount12(
						all_codes[i] & all_codes[k])) + (weight_k * popcount12(
						all_codes[i] & all_codes[j])))) + 2 * weight_i * weight_j * weight_k;

				int index = THREEDIMMINUS3 - weight_i - weight_j - weight_k;
				if (index >= 0) {
					triple_weight_polynomial[index] += 6 * koeff;
				}
			}
		}
	}
	// b^2a (untere)
	for (int i = 0; i < NUM_CODEWORDS; ++i) {
		for (int k = 0; k < i; ++k) {
			int weight_i = popcount12(all_codes[i]);
			int weight_k = popcount12(all_codes[k]);
			int koeff =
			DIMDIM * popcount12(all_codes[i] & all_codes[k]) - DIM * ((2 * (weight_i * popcount12(
					all_codes[i] & all_codes[k]))) + (weight_k * popcount12(all_codes[i]))) + 2 * weight_i * weight_i * weight_k;
			int index = THREEDIMMINUS3 - (2 * weight_i) - weight_k;
			if (index >= 0) {
				triple_weight_polynomial[index] += 3 * koeff;
			}
		}
	}
	// b^2c (obere)
	for (int i = 0; i < NUM_CODEWORDS; ++i) {
		for (int k = i + 1; k < NUM_CODEWORDS; ++k) {
			int weight_i = popcount12(all_codes[i]);
			int weight_k = popcount12(all_codes[k]);
			int koeff =
			DIMDIM * popcount12(all_codes[i] & all_codes[k]) - DIM * ((2 * (weight_i * popcount12(
					all_codes[i] & all_codes[k]))) + (weight_k * popcount12(all_codes[i]))) + 2 * weight_i * weight_i * weight_k;
			int index = THREEDIMMINUS3 - (2 * weight_i) - weight_k;
			if (index >= 0) {
				triple_weight_polynomial[index] += 3 * koeff;
			}
		}
	}
	// a^3
	for (int i = 0; i < NUM_CODEWORDS; ++i) {
		int weight_i = popcount12(all_codes[i]);
		int koeff = DIMDIM * popcount12(all_codes[i]) - DIM * (3 * (weight_i * popcount12(
				all_codes[i]))) + 2 * weight_i * weight_i * weight_i;

		int index = THREEDIMMINUS3 - (3 * weight_i);
		if (index >= 0) {
			triple_weight_polynomial[index] += koeff;
		}
	}
}

// Vektor an Liste anhaengen
void add_vec(list_node* liste, unsigned int vector) {
	list_node* new_item = (list_node*) malloc(sizeof(list_node));
	if (new_item == NULL) {
		printf("Fehler bei Zuordnung von Speicher!\n");
		exit(EXIT_FAILURE);
	}

	new_item->vector = vector;
	list_node* tmp = liste->next;
	liste->next = new_item;
	new_item->next = tmp;
}

// Ausgabe eines Gewichtspolynoms, dim_faktor = 1: hamming,
// dim_faktor = 2: doppel, dim_faktor = 3: triple
void print_wp(int* weight_polynomial, int dim_faktor) {
	printf("[");
	for (int i = 0; i <= DIM * dim_faktor; ++i) {
		printf(" %i", weight_polynomial[i]);
	}
	printf(" ]");
}

// Haming Poly aus den Codewoertern generieren
void gen_hamming_weight_polynomial(unsigned int* all_codes,
		int* hamming_weight_polynomial) {
	for (int i = 0; i < NUM_CODEWORDS; ++i) {
		hamming_weight_polynomial[popcount12(all_codes[i])] += 1;
	}
}


// Doppel Poly aus den Codewoertern generieren
// Liesze sich aehnlich wie die Triple-Weight-Funktion optimieren, da diese aber
// sowieso wenig Laufzeit hat, kann dies erstmal unterbleiben.
void gen_double_weight_polynomial(unsigned int* all_codes, int* hamming_weight_polynomial) {
	for (int i = 0; i < NUM_CODEWORDS; ++i) {
		for (int j = 0; j < NUM_CODEWORDS; ++j) {
			int weight1 = popcount12(all_codes[i]);
			int weight2 = popcount12(all_codes[j]);
			// Trick: <c1, c2> = w( c1 BIT_AND c2)
			int koeff = DIM * popcount12(all_codes[i] & all_codes[j]) - weight1 * weight2;

			int index = 2 * DIM - 2 - weight1 - weight2;
			if (index >= 0) {
				hamming_weight_polynomial[index] += koeff;
			}
		}
	}
}

// Alle Codewoerter aus den Generatorvektoren generieren
void gen_all_codes(int* generators, unsigned int* all_codewords) {
	int codeword_index = 1;
	all_codewords[codeword_index] = generators[codeword_index];
	for (int i = 0; i < RANK; ++i) {
		int tmp_codeword_index = codeword_index;
		for (int j = 0; j < tmp_codeword_index; ++j) {
			all_codewords[codeword_index++] = generators[i] ^ all_codewords[j];
		}
	}
}

// Einen Code als Erzeugermatrix und Invarianten auf
// den Bildschirm schreiben und in die gefunden.txt speichern
void print_code(codes* code) {
	printf("Erzeuger1: ");
	showbits(code->generator1);
	printf("\n");
	printf("Erzeuger2: ");
	showbits(code->generator2);
	printf("\n");
	printf("Erzeuger3: ");
	showbits(code->generator3);
	printf("\n");
	printf("Erzeuger4: ");
	showbits(code->generator4);
	printf("\n");
	printf("Erzeuger5: ");
	showbits(code->generator5);
	printf("\n");
	printf("Erzeuger6: ");
	showbits(code->generator6);
	printf("\n");
	printf("Invarianten 1 und 2: %s\n", code->invariants_key);
	printf("Triple-Weight: ");
	print_wp(code->triple_weight, 3);
	printf("\n");

	showbits_file(code->generator1);
	fprintf(erfolg, "\n");
	showbits_file(code->generator2);
	fprintf(erfolg, "\n");
	showbits_file(code->generator3);
	fprintf(erfolg, "\n");
	showbits_file(code->generator4);
	fprintf(erfolg, "\n");
	showbits_file(code->generator5);
	fprintf(erfolg, "\n");
	showbits_file(code->generator6);
	fprintf(erfolg, "\n");

	fprintf(erfolg, "[");
	for (int i = 0; i < NUM_KOEFF_HAMMING; ++i) {
		fprintf(erfolg, " %i", (code->hamming_weight)[i]);
	}
	fprintf(erfolg, " ]");
	fprintf(erfolg, "\n");

	fprintf(erfolg, "[");
	for (int i = 0; i < NUM_KOEFF_DOUBLE; ++i) {
		fprintf(erfolg, " %i", (code->doube_weight)[i]);
	}
	fprintf(erfolg, " ]");
	fprintf(erfolg, "\n");

	fprintf(erfolg, "[");
	for (int i = 0; i < NUM_KOEFF_TRIPLE; ++i) {
		fprintf(erfolg, " %i", (code->triple_weight)[i]);
	}
	fprintf(erfolg, " ]");
	fprintf(erfolg, "\n");
}

// Hashtable ausgeben
void print_hash_table() {
	codes *s;
	int i = 0;
	for (s = codes_invarianten; s != NULL; s = s->hh.next) {
		i++;
		printf("%s\n", s->invariants_key);
	}
	printf("Die Hashtabelle hat %i Eintraege!\n", i);
}

// String-Repraesentation von Hamming und Doppel-Gewichtspolynom
// fuer den Schluessel-Eintrag der Hashtabelle generieren,
// hier keine Schleife wegen maximaler Performance
void gen_key(char* key, int* hamming_weight_polynomial, int* double_weight_polynomial) {
	int n = sprintf(key, "%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_"
			"%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_"
			"%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_"
			"%i_%i_%i_%i_%i_%i_%i_%i", hamming_weight_polynomial[0],
			hamming_weight_polynomial[1], hamming_weight_polynomial[2],
			hamming_weight_polynomial[3], hamming_weight_polynomial[4],
			hamming_weight_polynomial[5], hamming_weight_polynomial[6],
			hamming_weight_polynomial[7], hamming_weight_polynomial[8],
			hamming_weight_polynomial[9], hamming_weight_polynomial[10],
			hamming_weight_polynomial[11], hamming_weight_polynomial[12],
			double_weight_polynomial[0], double_weight_polynomial[1],
			double_weight_polynomial[2], double_weight_polynomial[3],
			double_weight_polynomial[4], double_weight_polynomial[5],
			double_weight_polynomial[6], double_weight_polynomial[7],
			double_weight_polynomial[8], double_weight_polynomial[9],
			double_weight_polynomial[10], double_weight_polynomial[11],
			double_weight_polynomial[12], double_weight_polynomial[13],
			double_weight_polynomial[14], double_weight_polynomial[15],
			double_weight_polynomial[16], double_weight_polynomial[17],
			double_weight_polynomial[18], double_weight_polynomial[19],
			double_weight_polynomial[20], double_weight_polynomial[21],
			double_weight_polynomial[22], double_weight_polynomial[23],
			double_weight_polynomial[24]);

	if (n < 0 || n > KEY_BUFF_SIZE) {
		printf("sprintf Fehlgeschlagen!");
		exit(1);
	}
}

// String-Repraesentation aller drei Gewichtspolynome
// fuer den Schluessel-Eintrag der Hashtabelle generieren,
// hier keine Schleife wegen maximaler Performance
void gen_key_all(char* key, int* hamming_weight_polynomial, int* double_weight_polynomial,
		int* triple_weight_polynomial) {
	int n = sprintf(key,

	"%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_"
			"%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_"
			"%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_"
			"%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i_%i",

	hamming_weight_polynomial[0], hamming_weight_polynomial[1],
			hamming_weight_polynomial[2], hamming_weight_polynomial[3],
			hamming_weight_polynomial[4], hamming_weight_polynomial[5],
			hamming_weight_polynomial[6], hamming_weight_polynomial[7],
			hamming_weight_polynomial[8], hamming_weight_polynomial[9],
			hamming_weight_polynomial[10], hamming_weight_polynomial[11],
			hamming_weight_polynomial[12], double_weight_polynomial[0],
			double_weight_polynomial[1], double_weight_polynomial[2],
			double_weight_polynomial[3], double_weight_polynomial[4],
			double_weight_polynomial[5], double_weight_polynomial[6],
			double_weight_polynomial[7], double_weight_polynomial[8],
			double_weight_polynomial[9], double_weight_polynomial[10],
			double_weight_polynomial[11], double_weight_polynomial[12],
			double_weight_polynomial[13], double_weight_polynomial[14],
			double_weight_polynomial[15], double_weight_polynomial[16],
			double_weight_polynomial[17], double_weight_polynomial[18],
			double_weight_polynomial[19], double_weight_polynomial[20],
			double_weight_polynomial[21], double_weight_polynomial[22],
			double_weight_polynomial[23], double_weight_polynomial[24],
			triple_weight_polynomial[0], triple_weight_polynomial[1],
			triple_weight_polynomial[2], triple_weight_polynomial[3],
			triple_weight_polynomial[4], triple_weight_polynomial[5],
			triple_weight_polynomial[6], triple_weight_polynomial[7],
			triple_weight_polynomial[8], triple_weight_polynomial[9],
			triple_weight_polynomial[10], triple_weight_polynomial[11],
			triple_weight_polynomial[12], triple_weight_polynomial[13],
			triple_weight_polynomial[14], triple_weight_polynomial[15],
			triple_weight_polynomial[16], triple_weight_polynomial[17],
			triple_weight_polynomial[18], triple_weight_polynomial[19],
			triple_weight_polynomial[20], triple_weight_polynomial[21],
			triple_weight_polynomial[22], triple_weight_polynomial[23],
			triple_weight_polynomial[24], triple_weight_polynomial[25],
			triple_weight_polynomial[26], triple_weight_polynomial[27],
			triple_weight_polynomial[28], triple_weight_polynomial[29],
			triple_weight_polynomial[30], triple_weight_polynomial[31],
			triple_weight_polynomial[32], triple_weight_polynomial[33],
			triple_weight_polynomial[34], triple_weight_polynomial[35],
			triple_weight_polynomial[36]);

	if (n < 0 || n > KEY_BUFF_SIZE_ALL) {
		printf("sprintf Fehlgeschlagen!");
		exit(1);
	}
}

// Einen Code in der Form: Generatorvektoren als Int-Zahlen und Invarianten
// getrennt durch Leerzeichen pro Zeile in invariants.txt schreiben.
void logCode(codes* curr_code) {
	fprintf(invariants_txt, "%i %i %i %i %i %i ", curr_code->generator1,
			curr_code->generator2, curr_code->generator3, curr_code->generator4,
			curr_code->generator5, curr_code->generator6);
	fprintf(invariants_txt, "[");
	for (int i = 0; i < NUM_KOEFF_HAMMING; ++i) {
		fprintf(invariants_txt, " %i", curr_code->hamming_weight[i]);
	}
	fprintf(invariants_txt, " ] [");

	for (int i = 0; i < NUM_KOEFF_DOUBLE; ++i) {
		fprintf(invariants_txt, " %i", curr_code->doube_weight[i]);
	}
	fprintf(invariants_txt, " ] [");

	for (int i = 0; i < NUM_KOEFF_TRIPLE; ++i) {
		fprintf(invariants_txt, " %i", curr_code->triple_weight[i]);
	}
	fprintf(invariants_txt, " ] \n");
}

int main(void) {
	invariants_txt = fopen("data/invariants.txt", "w");
	if (!invariants_txt) {
		printf("Kann nicht auf data/invariants.txt zugreifen!\n");
		exit(EXIT_FAILURE);
	}
	setvbuf(invariants_txt, NULL, _IOLBF, BUFSIZ);

	erfolg = fopen("data/gefunden.txt", "w");
	if (!erfolg) {
		printf("Kann nicht auf data/gefunden.txt zugreifen!\n");
		exit(EXIT_FAILURE);
	}
	setvbuf(erfolg, NULL, _IOLBF, BUFSIZ);

	// Die Vektoren schnell ueber Prefix und Gewicht zugaenglich machen
	// Wichtig: Nullten Eintrag ignorieren!
	list_node* vec_per_weight[NUM_PREFIX][NUM_WEIGHTS_BASIC];

	// Initialisiere vec_per_weight, da add_vec eine Vorhandene Liste
	// vorraussetzt, ersten Eintrag als Kopf initialisieren.
	// Wert von Head ignorieren!
	for (int pref = 0; pref < NUM_PREFIX; ++pref) {
		for (int i = 0; i < NUM_WEIGHTS_BASIC; ++i) {
			list_node* head = (list_node*) malloc(sizeof(list_node));
			if (head == NULL) {
				printf("Fehler bei Zuordnung von Speicher!\n");
				exit(EXIT_FAILURE);
			}
			head->vector = 0;
			head->next = NULL;
			vec_per_weight[pref][i] = head;
		}
	}

	// Als Generatorenvektoren kommen nur Vektoren mit einer 1 in den ersten
	// 6 Stellen und den 64 anderen Werten in den letzten Stellen in Frage
	unsigned int prefix;
	for (int i = RANK; i < DIM; ++i) {
		prefix = (unsigned int) (1 << i);
		for (int j = 0; j < NUM_VECTORS_WITH_PREFIX; ++j) {
			g_vectors[i - RANK][j] = (unsigned int) (prefix + j);
		}
	}

	// vec_per_weight als Array von Listen der Form
	// [Prefix, Gewicht] -> Liste von Vektoren anlegen
	for (int pref = 0; pref < NUM_PREFIX; ++pref) {
		for (int vec = 0; vec < NUM_VECTORS_WITH_PREFIX; ++vec) {
			int hamming_weight = popcount12(g_vectors[pref][vec]);
			add_vec(vec_per_weight[pref][hamming_weight], g_vectors[pref][vec]);
		}
	}

	// Kombinationen der Gewichte generieren
	unsigned int possible_weight_combs[NUM_MAX_COMBS][RANK];
	int q = 0;
	for (int i = 7; i >= 0; --i)
		for (int j = i; j >= 0; --j)
			for (int k = j; k >= 0; --k)
				for (int l = k; l >= 0; --l)
					for (int m = l; m >= 0; --m)
						for (int n = m; n >= 0; --n) {
							possible_weight_combs[q][0] = i;
							possible_weight_combs[q][1] = j;
							possible_weight_combs[q][2] = k;
							possible_weight_combs[q][3] = l;
							possible_weight_combs[q][4] = m;
							possible_weight_combs[q][5] = n;
							q++;
						}

	time_t start = time(NULL);

	// Alle Kombinationen von Generatorvektoren durchlaufen
	unsigned long long int cnt_cnt = 0;
	for (int i = 0; i < NUM_MAX_COMBS; ++i)
		for_each_item_next(vec1, vec_per_weight[5][possible_weight_combs[i][0]])
			for_each_item_next(vec2, vec_per_weight[4][possible_weight_combs[i][1]])
				for_each_item_next(vec3, vec_per_weight[3][possible_weight_combs[i][2]])
					for_each_item_next(vec4, vec_per_weight[2][possible_weight_combs[i][3]])
						for_each_item_next(vec5, vec_per_weight[1][possible_weight_combs[i][4]])
							for_each_item_next(vec6, vec_per_weight[0][possible_weight_combs[i][5]])
							{
								cnt_cnt++;

								unsigned int all_codes[NUM_CODEWORDS] = { 0 };
								int generators[RANK] =
								{ vec1->vector, vec2->vector, vec3->vector,
								  vec4->vector, vec5->vector, vec6->vector };
								gen_all_codes(generators, all_codes);

								int hamming_weight_polynomial[NUM_KOEFF_HAMMING] = { 0 };
								gen_hamming_weight_polynomial(all_codes, hamming_weight_polynomial);

								int double_weight_polynomial[NUM_KOEFF_DOUBLE] = { 0 };
								gen_double_weight_polynomial(all_codes, double_weight_polynomial);

								int triple_weight_polynomial[NUM_KOEFF_TRIPLE] = { 0 };
								gen_triple_weight_polynomial(all_codes, triple_weight_polynomial);

								char key[KEY_BUFF_SIZE];
								gen_key(key, hamming_weight_polynomial, double_weight_polynomial);

								codes* suche;
								HASH_FIND_STR(codes_invarianten, &(key), suche);

								if (suche == NULL) {
									printf("Not in Hashtable, adding...%s\n", key);

									codes* curr_code = (codes*) malloc(sizeof(codes));
									if (curr_code == NULL) {
										printf("Fehler bei Zuordnung von Speicher!\n");
										exit(EXIT_FAILURE);
									}
									curr_code->generator1 = vec1->vector;
									curr_code->generator2 = vec2->vector;
									curr_code->generator3 = vec3->vector;
									curr_code->generator4 = vec4->vector;
									curr_code->generator5 = vec5->vector;
									curr_code->generator6 = vec6->vector;

									memcpy(curr_code->hamming_weight,
											hamming_weight_polynomial,
											NUM_KOEFF_HAMMING * sizeof(int));

									memcpy(curr_code->doube_weight,
											double_weight_polynomial,
											NUM_KOEFF_TRIPLE * sizeof(int));

									memcpy(curr_code->triple_weight,
											triple_weight_polynomial,
											NUM_KOEFF_TRIPLE * sizeof(int));

									memcpy(curr_code->invariants_key, key,
											KEY_BUFF_SIZE * sizeof(char));

									HASH_ADD_STR(codes_invarianten, invariants_key,
											curr_code);

									logCode(curr_code);
								} else {
									int m = memcmp(suche->triple_weight,
											triple_weight_polynomial,
											NUM_KOEFF_TRIPLE * sizeof(int));
									if (m != 0) {
										char key_sig[KEY_BUFF_SIZE_ALL];
										gen_key_all(key_sig, hamming_weight_polynomial,
												double_weight_polynomial,
												triple_weight_polynomial);

										codes_known* suche_sig;
										HASH_FIND_STR(codes_known_sigs, &(key_sig), suche_sig);
										if (suche_sig == NULL) {
											printf("WE FOUND SOMETHING!:\n");
											printf("First Code:\n");
											fprintf(erfolg, "First Code:\n");
											print_code(suche);
											printf("Second Code:\n");

											codes* curr_code = (codes*) malloc(
													sizeof(codes));
											if (curr_code == NULL) {
												printf("Fehler bei Zuordnung von Speicher!\n");
												exit(EXIT_FAILURE);
											}
											curr_code->generator1 = vec1->vector;
											curr_code->generator2 = vec2->vector;
											curr_code->generator3 = vec3->vector;
											curr_code->generator4 = vec4->vector;
											curr_code->generator5 = vec5->vector;
											curr_code->generator6 = vec6->vector;

											memcpy(curr_code->hamming_weight,
													hamming_weight_polynomial,
													NUM_KOEFF_HAMMING * sizeof(int));

											memcpy(curr_code->doube_weight,
													double_weight_polynomial,
													NUM_KOEFF_TRIPLE * sizeof(int));

											memcpy(curr_code->triple_weight,
													triple_weight_polynomial,
													NUM_KOEFF_TRIPLE * sizeof(int));

											memcpy(curr_code->invariants_key, key,
													KEY_BUFF_SIZE * sizeof(char));

											fprintf(erfolg, "Second Code:\n");
											print_code(curr_code);
											fprintf(erfolg, "-------------------------\n");

											free(curr_code);

											codes_known* code_sig = (codes_known*) malloc(
													sizeof(codes_known));
											if (code_sig == NULL) {
												printf("Fehler bei Zuordnung von Speicher!\n");
												exit(EXIT_FAILURE);
											}

											memcpy(code_sig->invariants_key_all, key_sig,
													KEY_BUFF_SIZE_ALL * sizeof(char));

											HASH_ADD_STR(codes_known_sigs,
															invariants_key_all, code_sig);
										}
									}
								}

								if (cnt_cnt % 50000 == 0) {
									print_wp(hamming_weight_polynomial, 1);
									printf("\n");
									print_wp(double_weight_polynomial, 2);
									printf("\n");
									print_wp(triple_weight_polynomial, 3);
									printf("\n");
									printf("-------------- %llu\n", cnt_cnt);
									double zeit_bisher = (double) (time(
									NULL) - start);
									printf("Zeit bisher: %.2f\n", zeit_bisher);

									int sekunden_to_go = (int) (((double) ANZ_CODES / (double) cnt_cnt)
																* zeit_bisher) - zeit_bisher;
									int days_to_go = (int) (((sekunden_to_go / 60) / 60) / 24);
									int hours_to_go = (int) ((sekunden_to_go - (days_to_go * 24
															  * 60 * 60))) / (60 * 60);
									int minutes_to_go = (int) (sekunden_to_go - (
																(days_to_go * 24 * 60 * 60)
																+ (hours_to_go * 60 * 60))) / 60;
									printf("Erwartete Zeit bis zum Ende: %is (%i Tag(e), "
											"%i Stunde(n), %i Minute(n))\n",
											sekunden_to_go, days_to_go, hours_to_go,
											minutes_to_go);
								}
							}

	fclose(invariants_txt);
	fclose(erfolg);
	printf("Programm erfolgreich durchgelaufen!\n");

	return EXIT_SUCCESS;
}
