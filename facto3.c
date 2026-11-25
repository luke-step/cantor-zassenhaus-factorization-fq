#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <malloc.h>
#include <gmp.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fq_default.h>
#include <flint/fq_default_poly.h>
#include <time.h>

fq_default_ctx_t F; // Déclare le corps F 
const char *var = "t"; // Déclare la variable
fq_default_poly_t f_init, H, Q, R, rem, f_simple, b, f_der, neg_one, Pj, pol;
fq_default_poly_t *f_s = &f_simple;
fq_default_poly_t *ptb = &b;
fq_default_poly_t *pj = &Pj;
fq_default_poly_t *poly = &pol;
fq_default_t coeff; 
fq_default_t p_one, n_one;
fmpz_t premier, pw, carac;
int it, deg, compteur, sizefact, degmaxirred, nb, p_int, d_int, n; // p_int = caractéristique, n = degré de f_init
int *ptdeg = &deg; 
int compteur_global = 0;
int *r = &compteur_global;
int compteur_irred1 = 0;
clock_t global_start;

// Fonction pour définir un t^(q^j)-t de façon économe
fq_default_poly_t *Prodj(fq_default_poly_t *pj, const int j) {
    fq_default_poly_clear(*pj, F);
    fq_default_poly_init2(*pj, 2, F);
    fmpz_mul(pw, pw, carac);
    fq_default_poly_set_coeff(*pj, fmpz_get_ui(pw), p_one, F);
    fq_default_poly_set_coeff(*pj, 1, n_one, F);
    return pj;
};

// Fonction de réduction pour obtenir un polynôme sans facteur carré
fq_default_poly_t *reduction_fq(fq_default_poly_t *f_s, const fq_default_poly_t f_init) {
    fq_default_poly_set(*f_s, f_init, F); 
    fq_default_poly_init(f_der, F);
    fq_default_poly_init(H, F);
    fq_default_poly_init(Q, F);
    fq_default_poly_init(R, F);
    // Calcul de la dérivée
    fq_default_poly_derivative(f_der, *f_s, F);
    if (fq_default_poly_is_zero(f_der, F)) {
        // f est une puissance de p, on prend la racine p-ième
        fq_default_poly_pow(*f_s, *f_s, (slong)(carac - 1), F);
    } else {
        // f n'est pas une puissance de p, on divise par h = pgcd(f, f')
        fq_default_poly_gcd(H, *f_s, f_der, F);
        fq_default_poly_divrem(Q, R, *f_s, H, F);
        fq_default_poly_set(*f_s, Q, F);
    }
    // Clear
    fq_default_poly_clear(H, F);
    fq_default_poly_clear(R, F);
    fq_default_poly_clear(Q, F);
    fq_default_poly_clear(f_der, F);
    fq_default_poly_make_monic(*f_s, *f_s, F);
    return f_s;
};

int split(fq_default_poly_t **liste) {
    fq_default_poly_init(*pj,F);
    fmpz_init(pw);
    fq_default_init(p_one, F);
    fq_default_init(n_one, F);
    fq_default_one(p_one, F);
    fq_default_neg(n_one, p_one, F);
    int n = (int)floor((float)deg / 2 + 1);
    fmpz_one(pw);
    it = 0;
    while (it < n) {
        it++;
        fq_default_poly_gcd(liste[it][0], *Prodj(pj, it), f_simple, F); 
        fq_default_poly_divrem(f_simple, rem, f_simple, liste[it][0], F);
        n = (int)floor((float)deg / 2 + 1);
        if(fq_default_poly_is_one(f_simple,F)){
            break;
        }
    }
    if (!fq_default_poly_is_one(f_simple, F)) {
        it++;
        fq_default_poly_set(liste[it][0], f_simple, F);
    }
    fq_default_poly_clear(rem, F);
    fmpz_clear(pw);
    fq_default_clear(p_one, F);
    fq_default_clear(n_one, F);
    return it;
}

// Génère un polynôme aléatoire non nul de degré au plus w (différent de 1)
fq_default_poly_t *randomPoly(fq_default_poly_t *poly,const int w){
    fq_default_init(coeff, F);
    fq_default_poly_zero(*poly, F); 
    while(1){
        if(fq_default_poly_is_zero(*poly,F) || (fq_default_poly_degree(*poly,F) == 0)){
            for(int i = 0; i < w; i++){
                fq_default_set_ui(coeff,(ulong)rand()%p_int,F);
                fq_default_poly_set_coeff(*poly,rand()%w,coeff,F);
            }
        }
        else{
            break;
        }
    }
    fq_default_poly_print_pretty(*poly,var,F);
    fq_default_clear(coeff, F);
    return poly;
}

// Algorithme de Cantor–Zassenhaus (cz) avec arrêt après 10 itérations si ptb reste trivial
fq_default_poly_t *cz(fq_default_poly_t *p, const int s) {
    // Si le degré de p est égal à s, p est considéré comme irréductible.
    if (fq_default_poly_degree(*p, F) == s) {
        return p;
    }
    ulong degre, m;
    fq_default_poly_init(neg_one, F); 
    fq_default_poly_init(rem, F);
    fmpz_init(pw);
    fq_default_poly_one(neg_one, F);
    fq_default_poly_neg(neg_one, neg_one, F);   
    fmpz_pow_ui(pw, carac, (ulong)s);  // pw = carac^s
    m = (fmpz_get_ui(pw) - 1) / 2;       // m = (p^s - 1)/2  
    ptb = randomPoly(ptb, fq_default_poly_degree(*p, F));
    fq_default_poly_powmod_ui_binexp(*ptb, *ptb, m, *p, F);  // b^m mod p
    int counter = 0;
    while ((fq_default_poly_is_zero(*ptb, F) || (fq_default_poly_degree(*ptb,F)) == 0 ) && (counter < 1000)) {
        ptb = randomPoly(ptb, fq_default_poly_degree(*p, F));                   
        fq_default_poly_powmod_ui_binexp(*ptb, *ptb, m, *p, F);
        counter++;
    }
    if (counter >= 1000) {
        printf("le poly est surement irred");
        return p;
    }
    fq_default_poly_gcd(rem, *p, *ptb, F);
    if (!(fq_default_poly_is_one(rem, F) || fq_default_poly_equal(rem,*p,F))){
        fq_default_poly_swap(*p, rem, F);
    } else {
        fq_default_poly_add(*ptb, *ptb, neg_one, F);
        fq_default_poly_gcd(*p, *ptb, *p, F);
    }
    fq_default_poly_clear(neg_one, F);
    fq_default_poly_clear(rem, F);
    fmpz_clear(pw);
    // Vérification avant récursion pour éviter de relancer avec p = 1.
    if (fq_default_poly_is_one(*p, F)){
        return p;}
    return cz(p, s);
    
};

fq_default_poly_t *Factor(fq_default_poly_t **liste, fq_default_poly_t **sortie) {
    for (int k = 0; k < sizefact ; k++) {         // Parcourt les éléments de notre liste f_s
        while (!fq_default_poly_is_one(liste[k][0], F)) {
            int d = fq_default_poly_degree(liste[k][0], F);
            if(d == k) {
                fq_default_poly_set(sortie[*r][0], liste[k][0], F);
                fq_default_poly_divrem(liste[k][0], pol, liste[k][0], sortie[*r][0], F);
            } 
            else {
                fq_default_poly_set(*poly, liste[k][0], F);
                // On passe le degré effectif du polynôme au lieu de k
                cz(poly, k);
                fq_default_poly_set(sortie[*r][0], pol, F);
                fq_default_poly_divrem(liste[k][0], pol, liste[k][0], sortie[*r][0], F);
            }
            if(!fq_default_poly_is_one(sortie[*r][0],F)){
            printf("\n-----------------------");
            printf("\nun irréductible = ");
            fq_default_poly_print_pretty(sortie[*r][0], var, F);
            printf("\n-----------------------");
            }
            // Vérification si l'irréductible affiché est égal à 1
            if (0 == fq_default_poly_degree(sortie[*r][0], F)) {
                compteur_irred1++;
                if (compteur_irred1 >= *r) {
                    printf("\n le polynôme est irrédictible.\n");
                    *r = - 99 ;
                    return NULL;
                }
            }
            (*r)++;
        }
        
    }
    return NULL;
};

void multiplicte(fq_default_poly_t **liste) {
    int m = 0;
    fq_default_poly_t temp, quo, local_rem;
    fq_default_poly_init(temp, F);
    fq_default_poly_init(quo, F);
    fq_default_poly_init(local_rem, F);
    // On travaille sur une copie de f_init pour ne pas le modifier
    fq_default_poly_set(temp, f_init, F);
    printf("\nLa factorisation de f en facteurs irréductibles (à unité près) est :\n");
    printf("f = ");
    int first = 1;
    int un = 0;
    if(*r < 0){
        printf("(");
        while(1){
            fq_default_poly_divrem(quo, local_rem, temp, f_simple, F);
            if (fq_default_poly_is_zero(local_rem, F)) {
                m++;
                fq_default_poly_swap(temp, quo, F);
            }      
            else {
                break;
            }
        }
        fq_default_poly_print_pretty(*f_s, var,F);
        printf(")^%d",m);
        return;
    }
    for (int j = 0; j < *r; j++){
        fq_default_poly_set(temp,f_init,F);
        m = 0;
        // On divise temp par le facteur liste[i][0] autant de fois que possible
        while (1) {
            fq_default_poly_divrem(quo, local_rem, temp, liste[j][0], F);
            if (fq_default_poly_is_zero(local_rem, F)){
                m++;
                fq_default_poly_set(temp, quo, F);
            }
            else {
                break;
            }
            }
        printf(" (");
        fq_default_poly_print_pretty(liste[j][0], var, F);
        printf(")^%d " , m);
    }
    printf("\n\n");
    fq_default_poly_clear(temp, F);
    fq_default_poly_clear(quo, F);
    fq_default_poly_clear(local_rem, F);
    return;
}

int main(){
    clock_t end;
    double cpu_time_used;
    global_start = clock();
    srand(time(NULL));
    
    printf("\n======================================================================\n");
    printf("       CONTEXTE\n");
    printf("======================================================================\n");
    printf("Nombre premier p différent de 2 : ");
    scanf("%d", &p_int);
    printf("Degré du polynôme f à factoriser : ");
    scanf("%d", &n);
    int *coeff_f_init = (int*)malloc((n+1) * sizeof(int));
    printf("Les %d coefficients du polynôme f\n", n+1); 
    for (int i = 0; i < n+1; i++){
        printf("Coefficient pour t^%d : ", i);
        scanf("%d", &coeff_f_init[i]); 
    }
    printf("======================================================================\n");
    printf("But : factoriser f = ");
    for (int i = 0; i < n+1; i++){
        printf("%d*t^%d", coeff_f_init[i], i);
        if (i != n){
            printf(" + ");
        }
    }
    printf("  dans F_%d\n", p_int);
    // INIT
    fmpz_init_set_ui(carac, p_int); 
    fq_default_ctx_init_type(F, carac, 1, var, 3); 
    fq_default_poly_init(f_init, F);
    fq_default_init(coeff, F); 
    for (int i = 0; i < n+1; i++){
        fq_default_set_ui(coeff, coeff_f_init[i], F);
        fq_default_poly_set_coeff(f_init, (ulong)i, coeff, F);
    }
    fq_default_clear(coeff, F); 
    fq_default_poly_init(f_simple, F);

    fq_default_poly_set(f_simple, *reduction_fq(f_s, f_init), F);
    printf("======================================================================\n");
    printf("\nPolynôme sans facteur carré f_simple = ");
    fq_default_poly_print_pretty(f_simple, "t", F);
    // Met à jour le degré à partir de f_simple
    deg = fq_default_poly_degree(f_simple, F);
    printf("   | degré : %d\n", deg);
    if (deg == 1) {
        printf("======================================================================\n");
        printf("f_simple est irréductible car de degré 1 : ");
        fq_default_poly_print_pretty(f_simple, "t", F);
        printf("\n\na factorisation de f en facteurs irréductibles (à unité près) est :\nf = (");
        fq_default_poly_print_pretty(f_simple, var, F);
        printf(")^%ld\n", fq_default_poly_degree(f_init, F));
        printf("======================================================================\n");
        end = clock();
        cpu_time_used = ((double)(end - global_start));
        printf("\n      TEMPS D'EXECUTION : %f tics\n",cpu_time_used);
        return 0;
    }
    
    // Allocation de fs (liste de polynômes)
    fq_default_poly_t **fs = (fq_default_poly_t**)malloc((deg+1) * sizeof(fq_default_poly_t*));
    if (fs == NULL) {
        printf("Erreur d'allocation mémoire pour fs\n");
        return -1;
    }
    for (int i = 0; i < deg+1; i++){
        fs[i] = (fq_default_poly_t*)malloc((deg+1) * sizeof(fq_default_poly_t));
        fq_default_poly_init(fs[i][0], F);
        fq_default_poly_one(fs[i][0], F);
    }
    
    degmaxirred = split(fs); 
    sizefact = degmaxirred * fq_default_poly_degree(fs[degmaxirred][0], F);
    
    nb = 0;
    for (int i = 0; i < degmaxirred + 1; i++){
        if (!(fq_default_poly_is_one(fs[i][0], F))) {
            nb++;
        }
    }

    if ((nb == 1) && (fq_default_poly_degree(fs[degmaxirred][0],F) == degmaxirred)){
        fq_default_poly_set(f_simple,*reduction_fq(f_s,f_init),F);
        int a = 0;
        fq_default_poly_init(rem,F);
        fq_default_poly_init(Q,F);
        while(1){
            fq_default_poly_divrem(Q,rem,f_init,fs[degmaxirred][0],F);
            if(fq_default_poly_is_zero(rem,F)){
                a++;
                fq_default_poly_set(f_init,Q,F);
            }
            else{
                break;
            }
        }
        printf("======================================================================\n");
        printf("a factorisation de f en facteurs irréductibles (à unité près) est :\nf = (");
        fq_default_poly_print_pretty(fs[degmaxirred][0],var,F);
        printf(")^%d",a);
        end = clock();
        cpu_time_used = ((double)(end - global_start));
        printf("\n      TEMPS D'EXECUTION : %f tics\n",cpu_time_used);
        return 0;
    }

    // Allocation de fact (liste des facteurs)
    fq_default_poly_t **fact = (fq_default_poly_t**)malloc((sizefact+1) * sizeof(fq_default_poly_t*));
    if (fact == NULL) {
        printf("Erreur d'allocation mémoire pour fact\n");
        return -1;
    }
    for (int i = 0; i < sizefact; i++){
        fact[i] = (fq_default_poly_t*)malloc((sizefact) * sizeof(fq_default_poly_t));
        fq_default_poly_init(fact[i][0], F);
        if (fact[i][0] == NULL){
            printf("Erreur d'allocation mémoire pour fact\n");
            return -1;
        }
    }
    
    // Factorisation
    fq_default_poly_init(b, F);
    fq_default_poly_init(pol, F);
    poly = &pol;
    Factor(fs,fact);
    multiplicte(fact);

    end = clock();
    cpu_time_used = ((double)(end - global_start));
    printf("\n      TEMPS D'EXECUTION : %f tics\n",cpu_time_used);
    return 0;
}