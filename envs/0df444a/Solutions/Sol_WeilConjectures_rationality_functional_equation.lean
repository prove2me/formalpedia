-- Prove2me | solution 1 for WeilConjectures.rationality_functional_equation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T16:35:42.955652+00:00
-- url     : https://prove2.me/submissions/b3285f9b-7752-4846-9367-ccf05c6229e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
import Theorems.Thm_FiniteFields_zetaFunction_integral_presentation
import Theorems.Thm_FiniteFields_zeta_functional_equation
import Theorems.Thm_WeilConjectures_projectiveSpace_zeta
import Theorems.Thm_WeilConjectures_weil_conjectures_curves

/-!
# Solution de `WeilConjectures.rationality_functional_equation` (fichier autonome)

FICHIER ENGENDRÉ par `scripts/assemble_solution.py rationality_functional_equation` à partir de la bibliothèque `Bridge` :
ne pas modifier à la main.

Il n'importe que Mathlib et des nœuds de la plateforme (définitions, et théorèmes PROVED du
projet FLT) ; les lemmes intermédiaires sont recopiés depuis `Bridge/` (espace de noms
`WeilConjectures.Bridge`).
-/

/-! ## Recopié de `Bridge/InverseRoots.lean` -/

section

/-!
# Racines inverses d'un polynôme de terme constant 1 (partie G)

Pour un polynôme `p` de terme constant `1` sur un corps algébriquement clos, les racines de son
polynôme réciproque `p.reverse` sont ses *racines inverses* : `p = ∏ (1 - a X)`. Quand `p`
vérifie de plus l'équation fonctionnelle `p_{2g-i} q^i = q^g p_i` (celle du L-polynôme d'une
courbe), ces racines sont stables par `a ↦ q / a`, et `p(1/(qt)) = q^{-g} t^{-2g} p(t)`.
-/

open Polynomial

namespace WeilConjectures.Bridge

section Reverse

variable {R S : Type*} [Semiring R] [Semiring S]

theorem reverse_map_of_injective (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reverse = p.reverse.map f := by
  ext n
  simp [coeff_reverse, coeff_map, natDegree_map_eq_of_injective hf]

theorem reverse_reverse_of_coeff_zero_ne_zero {p : R[X]} (h : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  have ht : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr h)
  have hd : p.reverse.natDegree = p.natDegree := by
    rw [reverse_natDegree, ht, Nat.sub_zero]
  ext n
  rw [coeff_reverse, hd, coeff_reverse, revAt_invol]

theorem reverse_one' : (1 : R[X]).reverse = 1 := by
  ext n
  rw [coeff_reverse, natDegree_one]
  rcases n with _ | n <;> simp [revAt]

end Reverse

section Field

variable {K : Type*} [Field K]

theorem reverse_X_sub_C (a : K) : (X - C a).reverse = 1 - C a * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_C]
  have hX : reflect 1 (X : K[X]) = 1 := by
    have := reflect_monomial (R := K) 1 1
    rwa [pow_one, revAt_le le_rfl, Nat.sub_self, pow_zero] at this
  rw [hX, pow_one]

theorem reverse_multiset_prod (s : Multiset K[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse_one']
  | cons a s ih => rw [Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-- Le polynôme réciproque d'un polynôme de terme constant `1` est unitaire. -/
theorem monic_reverse_of_coeff_zero_eq_one {p : K[X]} (h0 : p.coeff 0 = 1) : p.reverse.Monic := by
  rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by simp [h0]), h0]

/-- **Factorisation en racines inverses** : `p = ∏_{a} (1 - a X)`, où `a` parcourt les racines
du polynôme réciproque. -/
theorem eq_prod_one_sub_C_mul_X [IsAlgClosed K] {p : K[X]} (h0 : p.coeff 0 = 1) :
    p = (p.reverse.roots.map fun a ↦ 1 - C a * X).prod := by
  have hsplit : (p.reverse.roots.map fun a ↦ X - C a).prod = p.reverse :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_reverse_of_coeff_zero_eq_one h0)
      IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← reverse_reverse_of_coeff_zero_ne_zero (p := p) (by simp [h0]), ← hsplit]
  rw [reverse_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun a _ ↦ reverse_X_sub_C a

/-- Les racines du polynôme réciproque sont non nulles. -/
theorem ne_zero_of_mem_roots_reverse {p : K[X]} (hp : p ≠ 0) {a : K}
    (ha : a ∈ p.reverse.roots) : a ≠ 0 := by
  rintro rfl
  have h := (mem_roots (by simpa [reverse_eq_zero] using hp)).mp ha
  rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_reverse] at h
  exact hp (leadingCoeff_eq_zero.mp h)

/-- Les racines de `p` sont les inverses de celles de `p.reverse`. -/
theorem roots_eq_map_inv_roots_reverse [IsAlgClosed K] {p : K[X]} (h0 : p.coeff 0 = 1) :
    p.roots = p.reverse.roots.map (·⁻¹) := by
  have hp : p ≠ 0 := fun h ↦ by simp [h] at h0
  have hfac := eq_prod_one_sub_C_mul_X h0
  have hlin : ∀ a ∈ p.reverse.roots,
      (1 - C a * X : K[X]) = C (-a) * X - C (-1) := by
    intro a _
    simp only [C_neg, C_1]
    ring
  conv_lhs => rw [hfac, Multiset.map_congr rfl hlin]
  rw [roots_multiset_prod, Multiset.bind_map]
  · refine (Multiset.bind_congr fun a ha ↦ ?_).trans (Multiset.bind_singleton _ _)
    rw [roots_C_mul_X_sub_C _ (neg_ne_zero.mpr (ne_zero_of_mem_roots_reverse hp ha))]
    simp
  · rw [Multiset.mem_map]
    rintro ⟨a, ha, h⟩
    have := congrArg (coeff · 1) h
    simp [coeff_one] at this
    exact ne_zero_of_mem_roots_reverse hp ha this

end Field

section FunctionalEquation

variable {K : Type*} [Field K] {p : K[X]} {q : K} {g : ℕ}

/-- L'équation fonctionnelle force le degré exact `2g`. -/
theorem natDegree_eq_of_symm (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.natDegree = 2 * g := by
  refine le_antisymm hdeg (le_natDegree_of_ne_zero ?_)
  have := hsymm 0 (Nat.zero_le _)
  rw [Nat.sub_zero, pow_zero, mul_one, h0, mul_one] at this
  rw [this]
  exact pow_ne_zero _ hq

/-- Le polynôme réciproque est, à un scalaire près, `p (X / q)`. -/
theorem reverse_eq_C_mul_comp (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.reverse = C (q ^ g) * p.comp (C q⁻¹ * X) := by
  have hd := natDegree_eq_of_symm hq h0 hdeg hsymm
  ext i
  rw [coeff_reverse, hd, coeff_C_mul, comp_C_mul_X_coeff]
  by_cases hi : i ≤ 2 * g
  · rw [revAt_le hi, inv_pow, ← mul_assoc, ← hsymm i hi]
    field_simp
  · push Not at hi
    rw [← revAtFun_eq, revAtFun, if_neg (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- **Symétrie des racines inverses** : `a ↦ q / a` permute les racines de `p.reverse`. -/
theorem roots_reverse_map_div [IsAlgClosed K] (hq : q ≠ 0) (h0 : p.coeff 0 = 1)
    (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.reverse.roots.map (q / ·) = p.reverse.roots := by
  have hcomp : (p.comp (C q⁻¹ * X)).roots = p.roots.map (q * ·) := by
    have := roots_comp_C_mul_X_add_C p q⁻¹ 0 (isUnit_iff_ne_zero.mpr (inv_ne_zero hq))
    simpa [Ring.inverse_eq_inv'] using this
  conv_rhs => rw [reverse_eq_C_mul_comp hq h0 hdeg hsymm, roots_C_mul _ (pow_ne_zero _ hq),
    hcomp, roots_eq_map_inv_roots_reverse h0, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ ↦ by simp [div_eq_mul_inv]

/-- **Équation fonctionnelle sur les valeurs** : `p(1/(qt)) = q^{-g} t^{-2g} p(t)`. -/
theorem eval_inv_mul_eq (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) {t : K}
    (ht : t ≠ 0) :
    p.eval (q * t)⁻¹ = (q ^ g)⁻¹ * (t ^ (2 * g))⁻¹ * p.eval t := by
  have hd := natDegree_eq_of_symm hq h0 hdeg hsymm
  let := invertibleOfNonzero ht
  have h := eval₂_reverse_mul_pow (RingHom.id K) t p
  rw [invOf_eq_inv, reverse_eq_C_mul_comp hq h0 hdeg hsymm, hd] at h
  simp only [eval₂_id, eval_mul, eval_C, eval_comp, eval_X] at h
  rw [← h, mul_inv]
  field_simp

end FunctionalEquation

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/WeilAssembly.lean` -/

section

/-!
# Lemme d'assemblage W (partie N3)

`weil_conjectures` est l'énoncé de `riemann_hypothesis` (RH) augmenté de l'équation fonctionnelle
sur les valeurs (avec `ε = ±1`) et de la symétrie `α_{2n-i} = qⁿ / α_i`. On les déduit de RH et
de la **symétrie du diviseur** de `Z` sous `σ : a ↦ qⁿ / a`, que fournit le nœud
`rationality_functional_equation` (FE). Voir `docs/plan_lemme_W.md`.

Notations : `β_i = α_i` pour `1 ≤ i ≤ 2n - 1`, `β₀ = {1}`, `β_{2n} = {qⁿ}` ; le diviseur de `Z` est
la différence formelle `D⁺ - D⁻`, `D⁺ = Σ_{i impair} β_i`, `D⁻ = Σ_{i pair} β_i`.
-/

open Polynomial

namespace WeilConjectures.Bridge

section Assembly

open Classical

variable (q n : ℕ)

/-- `σ(a) = qⁿ / a` (involution de `ℂ`, avec `σ 0 = 0`). -/
noncomputable def reflectRoot (a : ℂ) : ℂ := (q : ℂ) ^ n / a

theorem reflectRoot_reflectRoot (hq : q ≠ 0) (a : ℂ) :
    reflectRoot q n (reflectRoot q n a) = a := by
  unfold reflectRoot
  have : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq)
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · field_simp

theorem reflectRoot_injective (hq : q ≠ 0) : Function.Injective (reflectRoot q n) :=
  Function.LeftInverse.injective (reflectRoot_reflectRoot q n hq)

/-- Les racines inverses `β_i`, avec `β₀ = {1}` et `β_{2n} = {qⁿ}`. -/
noncomputable def betaRoots (α : ℕ → Multiset ℂ) (i : ℕ) : Multiset ℂ :=
  if i = 0 then {1} else if i = 2 * n then {(q : ℂ) ^ n} else α i

/-- `D⁺ = Σ_{i impair} β_i`. -/
noncomputable def oddRoots (α : ℕ → Multiset ℂ) : Multiset ℂ :=
  ∑ i ∈ (Finset.range (2 * n + 1)).filter Odd, betaRoots q n α i

/-- `D⁻ = Σ_{i pair} β_i`. -/
noncomputable def evenRoots (α : ℕ → Multiset ℂ) : Multiset ℂ :=
  ∑ i ∈ (Finset.range (2 * n + 1)).filter Even, betaRoots q n α i

/-- Le diviseur `D⁺ - D⁻` est invariant par `σ` : `σ(D⁺) + D⁻ = D⁺ + σ(D⁻)`. -/
def DivisorSymm (α : ℕ → Multiset ℂ) : Prop :=
  (oddRoots q n α).map (reflectRoot q n) + evenRoots q n α =
    oddRoots q n α + (evenRoots q n α).map (reflectRoot q n)

/-- La symétrie des `β` : `β_j = σ(β_{2n-j})` pour `j ≤ 2n`. -/
def BetaSymm (α : ℕ → Multiset ℂ) : Prop :=
  ∀ j ≤ 2 * n, betaRoots q n α j = (betaRoots q n α (2 * n - j)).map (reflectRoot q n)

theorem betaRoots_of_mid (α : ℕ → Multiset ℂ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * n - 1) :
    betaRoots q n α i = α i := by
  unfold betaRoots
  rw [if_neg (by omega), if_neg (by omega)]

/-! ### Parité et réindexation `i ↦ 2n - i` -/

theorem odd_two_mul_sub_iff {i : ℕ} (hi : i ≤ 2 * n) : Odd (2 * n - i) ↔ Odd i := by
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

theorem even_two_mul_sub_iff {i : ℕ} (hi : i ≤ 2 * n) : Even (2 * n - i) ↔ Even i := by
  rw [Nat.even_iff, Nat.even_iff]
  omega

theorem mem_filter_odd_reflect {i : ℕ} (hi : i ∈ (Finset.range (2 * n + 1)).filter Odd) :
    2 * n - i ∈ (Finset.range (2 * n + 1)).filter Odd := by
  rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨by omega, (odd_two_mul_sub_iff n (by omega)).mpr hi.2⟩

theorem mem_filter_even_reflect {i : ℕ} (hi : i ∈ (Finset.range (2 * n + 1)).filter Even) :
    2 * n - i ∈ (Finset.range (2 * n + 1)).filter Even := by
  rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨by omega, (even_two_mul_sub_iff n (by omega)).mpr hi.2⟩

/-- Une somme sur les indices impairs (ou pairs) de `range (2n+1)` est invariante par
`i ↦ 2n - i`. -/
theorem sum_reflect {M : Type*} [AddCommMonoid M] (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i ≤ 2 * n, P (2 * n - i) ↔ P i) (g : ℕ → M) :
    ∑ i ∈ (Finset.range (2 * n + 1)).filter P, g (2 * n - i) =
      ∑ i ∈ (Finset.range (2 * n + 1)).filter P, g i := by
  refine Finset.sum_nbij' (fun i ↦ 2 * n - i) (fun i ↦ 2 * n - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, (hP i (by omega)).mpr hi.2⟩
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, (hP i (by omega)).mpr hi.2⟩
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    omega
  · intro i _
    rfl

theorem prod_reflect {M : Type*} [CommMonoid M] (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i ≤ 2 * n, P (2 * n - i) ↔ P i) (g : ℕ → M) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter P, g (2 * n - i) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter P, g i :=
  sum_reflect (M := Additive M) n P hP g

/-! ### W1 : poids et diviseur symétrique ⇒ symétrie des `β` -/

theorem filter_finset_sum {ι α : Type*} (p : α → Prop) [DecidablePred p] (s : Finset ι)
    (f : ι → Multiset α) :
    (∑ i ∈ s, f i).filter p = ∑ i ∈ s, (f i).filter p := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.filter_add, ih]

theorem map_finset_sum {ι α β : Type*} (g : α → β) (s : Finset ι) (f : ι → Multiset α) :
    (∑ i ∈ s, f i).map g = ∑ i ∈ s, (f i).map g :=
  map_sum (Multiset.mapAddMonoidHom g) f s

/-- Les poids `q^{i/2}` sont deux à deux distincts. -/
theorem weight_injective (hq : 1 < q) {i j : ℕ}
    (h : (q : ℝ) ^ ((i : ℝ) / 2) = (q : ℝ) ^ ((j : ℝ) / 2)) : i = j := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have h1 := (Real.rpow_le_rpow_left_iff hq').mp h.le
  have h2 := (Real.rpow_le_rpow_left_iff hq').mp h.ge
  have : (i : ℝ) = j := by linarith
  exact_mod_cast this

variable {q n}

/-- Les éléments de `β_i` ont pour module `q^{i/2}`. -/
theorem norm_betaRoots (α : ℕ → Multiset ℂ)
    (hw : ∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2))
    {i : ℕ} (hi : i ≤ 2 * n) {a : ℂ} (ha : a ∈ betaRoots q n α i) :
    ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2) := by
  unfold betaRoots at ha
  split_ifs at ha with h0 h2
  · subst h0
    rw [Multiset.mem_singleton.mp ha]
    simp
  · subst h2
    rw [Multiset.mem_singleton.mp ha, norm_pow, Complex.norm_natCast]
    rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  · exact hw i (by omega) (by omega) a ha

/-- Les éléments de `σ(β_i)` ont pour module `q^{(2n-i)/2}`. -/
theorem norm_reflect_betaRoots (hq : 1 < q) (α : ℕ → Multiset ℂ)
    (hw : ∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2))
    {i : ℕ} (hi : i ≤ 2 * n) {b : ℂ} (hb : b ∈ (betaRoots q n α i).map (reflectRoot q n)) :
    ‖b‖ = (q : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) := by
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [reflectRoot, norm_div, norm_pow, Complex.norm_natCast, norm_betaRoots α hw hi ha,
    Nat.cast_sub hi, ← Real.rpow_natCast, ← Real.rpow_sub hq0]
  congr 1
  push_cast
  ring

/-- **W1.** Poids et diviseur symétrique ⇒ `β_j = σ(β_{2n-j})`. -/
theorem betaSymm_of_weights (hq : 1 < q) (α : ℕ → Multiset ℂ)
    (hw : ∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2))
    (hsym : DivisorSymm q n α) : BetaSymm q n α := by
  intro j hj
  set w : ℝ := (q : ℝ) ^ ((j : ℝ) / 2)
  -- Filtrage par le module `w` : seuls `β_j` et `σ(β_{2n-j})` survivent.
  have hβ : ∀ i ≤ 2 * n, (betaRoots q n α i).filter (fun a ↦ ‖a‖ = w) =
      if i = j then betaRoots q n α i else 0 := by
    intro i hi
    split_ifs with hij
    · subst hij
      exact Multiset.filter_eq_self.mpr fun a ha ↦ norm_betaRoots α hw hi ha
    · refine Multiset.filter_eq_nil.mpr fun a ha h ↦ hij (weight_injective q hq ?_)
      rw [← norm_betaRoots α hw hi ha, h]
  have hσ : ∀ i ≤ 2 * n,
      ((betaRoots q n α i).map (reflectRoot q n)).filter (fun a ↦ ‖a‖ = w) =
        if i = 2 * n - j then (betaRoots q n α i).map (reflectRoot q n) else 0 := by
    intro i hi
    split_ifs with hij
    · refine Multiset.filter_eq_self.mpr fun b hb ↦ ?_
      rw [norm_reflect_betaRoots hq α hw hi hb, show 2 * n - i = j by omega]
    · refine Multiset.filter_eq_nil.mpr fun b hb h ↦ hij ?_
      have := weight_injective q hq ((norm_reflect_betaRoots hq α hw hi hb).symm.trans h)
      omega
  have hF := congrArg (Multiset.filter fun a ↦ ‖a‖ = w) hsym
  simp only [DivisorSymm, oddRoots, evenRoots, Multiset.filter_add, map_finset_sum,
    filter_finset_sum] at hF
  rw [Finset.sum_congr rfl fun i hi ↦ hσ i (by simp at hi; omega),
    Finset.sum_congr rfl fun i hi ↦ hβ i (by simp at hi; omega),
    Finset.sum_congr rfl fun i hi ↦ hβ i (by simp at hi; omega),
    Finset.sum_congr rfl fun i hi ↦ hσ i (by simp at hi; omega)] at hF
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_range] at hF
  rcases Nat.even_or_odd j with he | ho
  · have he' : Even (2 * n - j) := (even_two_mul_sub_iff n hj).mpr he
    have ho' : ¬ Odd (2 * n - j) := Nat.not_odd_iff_even.mpr he'
    have hno : ¬ Odd j := Nat.not_odd_iff_even.mpr he
    simp only [ho', hno, he, he', and_false, if_false, zero_add, add_zero, true_and,
      show j < 2 * n + 1 by omega, show 2 * n - j < 2 * n + 1 by omega] at hF
    exact hF
  · have ho' : Odd (2 * n - j) := (odd_two_mul_sub_iff n hj).mpr ho
    have he' : ¬ Even (2 * n - j) := Nat.not_even_iff_odd.mpr ho'
    have hne : ¬ Even j := Nat.not_even_iff_odd.mpr ho
    simp only [ho', hne, ho, he', and_false, if_false, zero_add, add_zero, true_and,
      show j < 2 * n + 1 by omega, show 2 * n - j < 2 * n + 1 by omega] at hF
    exact hF.symm

/-! ### W4 : symétrie des `α` (nœud FE) ⇒ diviseur symétrique -/

theorem betaSymm_of_alphaSymm (hq : q ≠ 0) (α : ℕ → Multiset ℂ)
    (hα : ∀ i, 1 ≤ i → i ≤ 2 * n - 1 → α (2 * n - i) = (α i).map (reflectRoot q n)) :
    BetaSymm q n α := by
  intro j hj
  have hqn : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq)
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [betaRoots, reflectRoot]
    · simp [betaRoots, reflectRoot, show 2 * n ≠ 0 by omega, hqn]
  · rcases eq_or_lt_of_le hj with rfl | hjlt
    · simp [betaRoots, reflectRoot, show 2 * n ≠ 0 by omega]
    · rw [betaRoots_of_mid q n α hj0 (by omega), betaRoots_of_mid q n α (by omega) (by omega)]
      have := hα (2 * n - j) (by omega) (by omega)
      rwa [show 2 * n - (2 * n - j) = j by omega] at this

/-- Sous `BetaSymm`, `σ(β_i) = β_{2n-i}`. -/
theorem map_reflect_betaRoots (hq : q ≠ 0) {α : ℕ → Multiset ℂ} (h : BetaSymm q n α) {i : ℕ}
    (hi : i ≤ 2 * n) :
    (betaRoots q n α i).map (reflectRoot q n) = betaRoots q n α (2 * n - i) := by
  rw [h (2 * n - i) (by omega), show 2 * n - (2 * n - i) = i by omega]

theorem divisorSymm_of_betaSymm (hq : q ≠ 0) {α : ℕ → Multiset ℂ} (h : BetaSymm q n α) :
    DivisorSymm q n α := by
  have hodd : (oddRoots q n α).map (reflectRoot q n) = oddRoots q n α := by
    rw [oddRoots, map_finset_sum, Finset.sum_congr rfl fun i hi ↦
      map_reflect_betaRoots hq h (by simp at hi; omega)]
    exact sum_reflect n Odd (fun i hi ↦ odd_two_mul_sub_iff n hi) _
  have heven : (evenRoots q n α).map (reflectRoot q n) = evenRoots q n α := by
    rw [evenRoots, map_finset_sum, Finset.sum_congr rfl fun i hi ↦
      map_reflect_betaRoots hq h (by simp at hi; omega)]
    exact sum_reflect n Even (fun i hi ↦ even_two_mul_sub_iff n hi) _
  rw [DivisorSymm, hodd, heven]

/-! ### Racines inverses d'une présentation -/

/-- Racines inverses de `A ∈ ℤ[X]` sur `ℂ` : les racines de `A.reverse`. -/
noncomputable def invRoots (A : ℤ[X]) : Multiset ℂ := (A.map (Int.castRingHom ℂ)).reverse.roots

variable (q n) in
/-- Les facteurs `P_i = ∏_{a ∈ β_i} (1 - a X)`, à racines inverses non nulles, pour `i ≤ 2n`. -/
def Factors (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ) : Prop :=
  ∀ i ≤ 2 * n, (P i).map (Int.castRingHom ℂ) =
      ((betaRoots q n α i).map fun a ↦ 1 - C a * X).prod ∧ ∀ a ∈ betaRoots q n α i, a ≠ 0

variable (q n) in
theorem factors_of (hq : q ≠ 0) (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ)
    (h0 : P 0 = 1 - Polynomial.X) (h2n : P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X)
    (hfac : ∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
      (P i).map (Int.castRingHom ℂ) = ((α i).map fun a ↦ 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) :
    Factors q n P α := by
  intro i hi
  have hqn : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [betaRoots, h0]
  · rcases eq_or_lt_of_le hi with rfl | hilt
    · simp [betaRoots, show 2 * n ≠ 0 by omega, h2n, hqn]
    · rw [betaRoots_of_mid q n α hi0 (by omega)]
      exact hfac i hi0 (by omega)

/-- Un polynôme de la forme `∏_{a ∈ β} (1 - a X)`, `a ≠ 0`, a `β` pour racines inverses. -/
theorem reverse_roots_of_prod {p : ℂ[X]} {β : Multiset ℂ}
    (hp : p = (β.map fun a ↦ 1 - C a * X).prod) (hβ : ∀ a ∈ β, a ≠ 0) :
    p.reverse.roots = β := by
  have h0 : p.coeff 0 = 1 := by
    rw [hp, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    exact Multiset.prod_eq_one fun x hx ↦ by
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx
      simp
  have hroots : p.roots = β.map (·⁻¹) := by
    have hlin : ∀ a ∈ β, (1 - C a * X : ℂ[X]) = C (-a) * X - C (-1) := by
      intro a _
      simp only [C_neg, C_1]
      ring
    rw [hp, Multiset.map_congr rfl hlin, roots_multiset_prod, Multiset.bind_map]
    · refine (Multiset.bind_congr fun a ha ↦ ?_).trans (Multiset.bind_singleton _ _)
      rw [roots_C_mul_X_sub_C _ (neg_ne_zero.mpr (hβ a ha))]
      simp
    · rw [Multiset.mem_map]
      rintro ⟨a, ha, h⟩
      have := congrArg (coeff · 1) h
      simp [coeff_one] at this
      exact hβ a ha this
  have := (roots_eq_map_inv_roots_reverse h0).symm.trans hroots
  exact Multiset.map_injective inv_injective this

/-- Racines inverses d'un produit de facteurs de terme constant 1. -/
theorem invRoots_prod (s : Finset ℕ) (P : ℕ → ℤ[X]) (hP : ∀ i ∈ s, (P i).coeff 0 = 1) :
    invRoots (∏ i ∈ s, P i) = ∑ i ∈ s, invRoots (P i) := by
  induction s using Finset.induction_on with
  | empty => simp [invRoots, reverse_one']
  | insert a s ha ih =>
    have hPa : (P a).map (Int.castRingHom ℂ) ≠ 0 := by
      intro h
      have := congrArg (coeff · 0) h
      simp [coeff_map, hP a (Finset.mem_insert_self a s)] at this
    have hs : (∏ i ∈ s, P i).map (Int.castRingHom ℂ) ≠ 0 := by
      rw [Polynomial.map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i hi h ↦ by
        have := congrArg (coeff · 0) h
        simp [coeff_map, hP i (Finset.mem_insert_of_mem hi)] at this
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih fun i hi ↦ hP i (Finset.mem_insert_of_mem hi),
      invRoots, invRoots, invRoots, Polynomial.map_mul, reverse_mul_of_domain, roots_mul]
    exact mul_ne_zero (by simpa [reverse_eq_zero] using hPa) (by simpa [reverse_eq_zero] using hs)

theorem coeff_zero_of_factors {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (h : Factors q n P α)
    {i : ℕ} (hi : i ≤ 2 * n) : (P i).coeff 0 = 1 := by
  have h1 := congrArg (coeff · 0) (h i hi).1
  simp only [coeff_map, eq_intCast] at h1
  conv_rhs at h1 => rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
  rw [Multiset.prod_eq_one fun x hx ↦ by
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx
    simp] at h1
  exact_mod_cast h1

/-- La présentation `Z · ∏_{pair} P_i = ∏_{impair} P_i` a pour diviseur `D⁺ - D⁻`. -/
theorem invRoots_odd {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (h : Factors q n P α) :
    invRoots (∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, P i) = oddRoots q n α := by
  rw [invRoots_prod _ _ fun i hi ↦ coeff_zero_of_factors h (by simp at hi; omega), oddRoots]
  exact Finset.sum_congr rfl fun i hi ↦
    reverse_roots_of_prod (h i (by simp at hi; omega)).1 (h i (by simp at hi; omega)).2

theorem invRoots_even {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (h : Factors q n P α) :
    invRoots (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, P i) = evenRoots q n α := by
  rw [invRoots_prod _ _ fun i hi ↦ coeff_zero_of_factors h (by simp at hi; omega), evenRoots]
  exact Finset.sum_congr rfl fun i hi ↦
    reverse_roots_of_prod (h i (by simp at hi; omega)).1 (h i (by simp at hi; omega)).2

/-! ### W3 : le diviseur ne dépend pas de la présentation -/

theorem map_ne_zero_of_coeff_zero {A : ℤ[X]} (hA : A.coeff 0 = 1) :
    A.map (Int.castRingHom ℂ) ≠ 0 := by
  intro h
  have := congrArg (coeff · 0) h
  simp [coeff_map, hA] at this

theorem invRoots_mul {A B : ℤ[X]} (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1) :
    invRoots (A * B) = invRoots A + invRoots B := by
  rw [invRoots, invRoots, invRoots, Polynomial.map_mul, reverse_mul_of_domain, roots_mul]
  exact mul_ne_zero (by simpa [reverse_eq_zero] using map_ne_zero_of_coeff_zero hA)
    (by simpa [reverse_eq_zero] using map_ne_zero_of_coeff_zero hB)

/-- L'image d'un polynôme entier dans `ℚ⟦X⟧`. -/
noncomputable abbrev toSeries (A : ℤ[X]) : PowerSeries ℚ :=
  ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ)

theorem toSeries_mul (A B : ℤ[X]) : toSeries (A * B) = toSeries A * toSeries B := by
  simp [toSeries, Polynomial.map_mul, Polynomial.coe_mul]

theorem toSeries_prod (s : Finset ℕ) (P : ℕ → ℤ[X]) :
    toSeries (∏ i ∈ s, P i) = ∏ i ∈ s, toSeries (P i) := by
  induction s using Finset.induction_on with
  | empty => simp [toSeries]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, toSeries_mul, ih]

theorem toSeries_injective : Function.Injective toSeries := by
  intro A B h
  have h1 : A.map (Int.castRingHom ℚ) = B.map (Int.castRingHom ℚ) := Polynomial.coe_inj.mp h
  exact Polynomial.map_injective _ (RingHom.injective_int _) h1

/-- Deux présentations `Z · B = A` ont « même diviseur ». -/
theorem invRoots_cross {Z : PowerSeries ℚ} {A₁ B₁ A₂ B₂ : ℤ[X]} (hA₁ : A₁.coeff 0 = 1)
    (hB₁ : B₁.coeff 0 = 1) (hA₂ : A₂.coeff 0 = 1) (hB₂ : B₂.coeff 0 = 1)
    (h₁ : Z * toSeries B₁ = toSeries A₁) (h₂ : Z * toSeries B₂ = toSeries A₂) :
    invRoots A₁ + invRoots B₂ = invRoots A₂ + invRoots B₁ := by
  have h : A₁ * B₂ = A₂ * B₁ := toSeries_injective (by
    rw [toSeries_mul, toSeries_mul, ← h₁, ← h₂]
    ring)
  rw [← invRoots_mul hA₁ hB₂, ← invRoots_mul hA₂ hB₁, h]

/-- Transfert de la symétrie d'un diviseur formel `a - b` (comptage). -/
theorem divisor_transfer {σ : ℂ → ℂ} (hσ : Function.Involutive σ) {a₁ b₁ a₂ b₂ : Multiset ℂ}
    (h₁ : a₁.map σ + b₁ = a₁ + b₁.map σ) (h : a₁ + b₂ = a₂ + b₁) :
    a₂.map σ + b₂ = a₂ + b₂.map σ := by
  have key : ∀ (s : Multiset ℂ) (y : ℂ), (s.map σ).count y = s.count (σ y) := fun s y ↦ by
    conv_lhs => rw [← hσ y]
    exact Multiset.count_map_eq_count' σ s hσ.injective (σ y)
  ext x
  have e1 := congrArg (Multiset.count x) h₁
  have e2 := congrArg (Multiset.count x) h
  have e3 := congrArg (Multiset.count (σ x)) h
  simp only [Multiset.count_add, key] at e1 e2 e3 ⊢
  omega

variable (q n) in
/-- **Symétrie du diviseur de `Z`** : pour une présentation `Z · B = A` (`A(0) = B(0) = 1`),
`σ(ρ(A)) + ρ(B) = ρ(A) + σ(ρ(B))`, où `ρ` désigne les racines inverses. -/
def ZetaDivisorSymm (Z : PowerSeries ℚ) : Prop :=
  ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧ Z * toSeries B = toSeries A ∧
    (invRoots A).map (reflectRoot q n) + invRoots B = invRoots A + (invRoots B).map (reflectRoot q n)

theorem coeff_zero_prod_of_factors {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (h : Factors q n P α)
    (S : ℕ → Prop) [DecidablePred S] :
    (∏ i ∈ (Finset.range (2 * n + 1)).filter S, P i).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  exact Finset.prod_eq_one fun i hi ↦ by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_of_factors h (by simp at hi; omega)]

/-- La présentation par les `P_i` a un diviseur symétrique dès que `Z` en a un. -/
theorem divisorSymm_of_zetaDivisorSymm (hq : q ≠ 0) {Z : PowerSeries ℚ} {P : ℕ → ℤ[X]}
    {α : ℕ → Multiset ℂ} (hF : Factors q n P α)
    (hZ : Z * ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, toSeries (P i) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, toSeries (P i))
    (hsym : ZetaDivisorSymm q n Z) : DivisorSymm q n α := by
  obtain ⟨A, B, hA, hB, hAB, hs⟩ := hsym
  rw [← toSeries_prod, ← toSeries_prod] at hZ
  have hc := invRoots_cross hA hB (coeff_zero_prod_of_factors hF Odd)
    (coeff_zero_prod_of_factors hF Even) hAB hZ
  rw [invRoots_odd hF, invRoots_even hF] at hc
  exact divisor_transfer (reflectRoot_reflectRoot q n hq) hs hc

/-- Et réciproquement, la symétrie des `β` donne celle du diviseur de `Z`. -/
theorem zetaDivisorSymm_of_betaSymm (hq : q ≠ 0) {Z : PowerSeries ℚ} {P : ℕ → ℤ[X]}
    {α : ℕ → Multiset ℂ} (hF : Factors q n P α)
    (hZ : Z * ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, toSeries (P i) =
      ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, toSeries (P i))
    (hB : BetaSymm q n α) : ZetaDivisorSymm q n Z := by
  refine ⟨_, _, coeff_zero_prod_of_factors hF Odd, coeff_zero_prod_of_factors hF Even,
    by rw [toSeries_prod, toSeries_prod]; exact hZ, ?_⟩
  rw [invRoots_odd hF, invRoots_even hF]
  exact divisorSymm_of_betaSymm hq hB

/-! ### W2 : symétrie des `β` ⇒ équation fonctionnelle sur les valeurs -/

theorem aeval_eq_prod {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (hF : Factors q n P α) {i : ℕ}
    (hi : i ≤ 2 * n) (x : ℂ) :
    aeval x (P i) = ((betaRoots q n α i).map fun a ↦ 1 - a * x).prod := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, (hF i hi).1, eval_multiset_prod,
    Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun a _ ↦ by simp

theorem prod_one_sub_mul_inv (hq : q ≠ 0) {β : Multiset ℂ} (hβ : ∀ a ∈ β, a ≠ 0) {t : ℂ}
    (ht : t ≠ 0) :
    (β.map fun a ↦ 1 - a * ((q : ℂ) ^ n * t)⁻¹).prod =
      (β.map fun a ↦ -a).prod * ((q : ℂ) ^ n * t)⁻¹ ^ β.card *
        (β.map fun a ↦ 1 - reflectRoot q n a * t).prod := by
  have hqn : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq)
  induction β using Multiset.induction_on with
  | empty => simp
  | cons a β ih =>
    have ha : a ≠ 0 := hβ a (Multiset.mem_cons_self a β)
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ,
      ih fun b hb ↦ hβ b (Multiset.mem_cons_of_mem hb), reflectRoot]
    field_simp
    ring

/-- Valeur de `P_i` en `1/(qⁿ t)`. -/
theorem aeval_inv_eq (hq : q ≠ 0) {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (hF : Factors q n P α)
    (hB : BetaSymm q n α) {i : ℕ} (hi : i ≤ 2 * n) {t : ℂ} (ht : t ≠ 0) :
    aeval (((q : ℂ) ^ n * t)⁻¹) (P i) =
      ((betaRoots q n α i).map fun a ↦ -a).prod * ((q : ℂ) ^ n * t)⁻¹ ^ (betaRoots q n α i).card *
        aeval t (P (2 * n - i)) := by
  rw [aeval_eq_prod hF hi, prod_one_sub_mul_inv hq (hF i hi).2 ht, aeval_eq_prod hF (by omega),
    ← map_reflect_betaRoots hq hB hi, Multiset.map_map]
  rfl

theorem natDegree_eq_card {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (hF : Factors q n P α) {i : ℕ}
    (hi : i ≤ 2 * n) : (P i).natDegree = (betaRoots q n α i).card := by
  have hlin : ∀ a : ℂ, (1 - C a * X : ℂ[X]) = C (-a) * X + C 1 := fun a ↦ by
    simp only [C_neg, C_1]
    ring
  rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)), (hF i hi).1,
    natDegree_multiset_prod _ (fun h ↦ ?_), Multiset.map_map]
  · rw [Multiset.map_congr rfl (g := fun _ ↦ 1) ?_, Multiset.map_const', Multiset.sum_replicate,
      smul_eq_mul, mul_one]
    intro a ha
    simp only [Function.comp_apply]
    rw [hlin, natDegree_linear (neg_ne_zero.mpr ((hF i hi).2 a ha))]
  · obtain ⟨a, ha, h0⟩ := Multiset.mem_map.mp h
    have := congrArg (coeff · 0) h0
    simp at this

/-- `(∏_{a ∈ β_i} (-a)) · (∏_{a ∈ β_{2n-i}} (-a)) = q^{n · #β_i}`. -/
theorem prod_neg_mul_reflect (hq : q ≠ 0) {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ}
    (hF : Factors q n P α) (hB : BetaSymm q n α) {i : ℕ} (hi : i ≤ 2 * n) :
    ((betaRoots q n α i).map fun a ↦ -a).prod *
        ((betaRoots q n α (2 * n - i)).map fun a ↦ -a).prod =
      ((q : ℂ) ^ n) ^ (betaRoots q n α i).card := by
  rw [← map_reflect_betaRoots hq hB hi, Multiset.map_map, ← Multiset.prod_map_mul,
    Multiset.map_congr rfl (g := fun _ ↦ (q : ℂ) ^ n), Multiset.map_const', Multiset.prod_replicate]
  intro a ha
  have := (hF i hi).2 a ha
  simp only [Function.comp_apply, reflectRoot]
  field_simp

variable (n) in
/-- L'exposant `χ = Σ (-1)^i deg P_i`. -/
def chi (P : ℕ → ℤ[X]) : ℤ := ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)

theorem chi_eq {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (hF : Factors q n P α) :
    chi n P = (∑ i ∈ (Finset.range (2 * n + 1)).filter Even, ((betaRoots q n α i).card : ℤ)) -
      ∑ i ∈ (Finset.range (2 * n + 1)).filter Odd, ((betaRoots q n α i).card : ℤ) := by
  rw [chi, ← Finset.sum_filter_add_sum_filter_not _ Even]
  have hodd : (Finset.range (2 * n + 1)).filter (fun i ↦ ¬ Even i) =
      (Finset.range (2 * n + 1)).filter Odd :=
    Finset.filter_congr fun i _ ↦ Nat.not_even_iff_odd
  rw [hodd, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_filter, Finset.mem_range] at hi
    rw [hi.2.neg_one_pow, one_mul, natDegree_eq_card hF (by omega)]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_filter, Finset.mem_range] at hi
    rw [hi.2.neg_one_pow, neg_one_mul, natDegree_eq_card hF (by omega)]

/-- Le produit des `P_i` (`i ∈ S`) en `1/(qⁿ t)`. -/
theorem prod_aeval_inv (hq : q ≠ 0) {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (hF : Factors q n P α)
    (hB : BetaSymm q n α) (S : ℕ → Prop) [DecidablePred S] (hS : ∀ i ≤ 2 * n, S (2 * n - i) ↔ S i)
    {t : ℂ} (ht : t ≠ 0) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter S, aeval (((q : ℂ) ^ n * t)⁻¹) (P i) =
      (∏ i ∈ (Finset.range (2 * n + 1)).filter S, ((betaRoots q n α i).map fun a ↦ -a).prod) *
        ((q : ℂ) ^ n * t)⁻¹ ^ (∑ i ∈ (Finset.range (2 * n + 1)).filter S, (betaRoots q n α i).card) *
        ∏ i ∈ (Finset.range (2 * n + 1)).filter S, aeval t (P i) := by
  rw [Finset.prod_congr rfl fun i hi ↦ aeval_inv_eq hq hF hB (by simp at hi; omega) ht,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    prod_reflect n S hS (fun i ↦ aeval t (P i))]

/-- Le carré du produit des constantes `∏_{a ∈ β_i}(-a)` sur `S` (stable par `i ↦ 2n - i`). -/
theorem sq_prod_neg (hq : q ≠ 0) {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ} (hF : Factors q n P α)
    (hB : BetaSymm q n α) (S : ℕ → Prop) [DecidablePred S] (hS : ∀ i ≤ 2 * n, S (2 * n - i) ↔ S i) :
    (∏ i ∈ (Finset.range (2 * n + 1)).filter S, ((betaRoots q n α i).map fun a ↦ -a).prod) ^ 2 =
      ((q : ℂ) ^ n) ^ (∑ i ∈ (Finset.range (2 * n + 1)).filter S, (betaRoots q n α i).card) := by
  rw [sq]
  conv_lhs => arg 2; rw [← prod_reflect n S hS (fun i ↦ ((betaRoots q n α i).map fun a ↦ -a).prod)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i hi ↦ prod_neg_mul_reflect hq hF hB (by simp at hi; omega)

theorem sq_const_eq {u co ce : ℂ} {A B : ℕ} {χ : ℤ} (hu : u ≠ 0) (hco : co ^ 2 = u ^ A)
    (hce : ce ^ 2 = u ^ B) (hχ : χ = (B : ℤ) - A) : (co / ce * u ^ χ) ^ 2 = u ^ χ := by
  rw [mul_pow, div_pow, hco, hce, ← zpow_natCast u A, ← zpow_natCast u B, ← zpow_sub₀ hu,
    ← zpow_natCast (u ^ χ) 2, ← zpow_mul, ← zpow_add₀ hu]
  congr 1
  rw [hχ]
  push_cast
  ring

/-- **W2.** Équation fonctionnelle sur les valeurs, avec `ε = ±1`. -/
theorem functional_equation_of_betaSymm (hq : 1 < q) {P : ℕ → ℤ[X]} {α : ℕ → Multiset ℂ}
    (hF : Factors q n P α) (hB : BetaSymm q n α) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      ∀ t : ℂ, t ≠ 0 →
        (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, aeval t (P i)) ≠ 0 →
        (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            aeval (((q : ℂ) ^ n * t)⁻¹) (P i)) ≠ 0 →
        (∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
              aeval (((q : ℂ) ^ n * t)⁻¹) (P i)) /
            (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
              aeval (((q : ℂ) ^ n * t)⁻¹) (P i)) =
          ε * (((q : ℝ) ^ ((n : ℝ) *
              ((∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ) : ℤ) : ℝ)
                / 2) : ℝ) : ℂ) *
            t ^ (∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) *
            ((∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, aeval t (P i)) /
              (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, aeval t (P i))) := by
  have hq0 : q ≠ 0 := by omega
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hu0 : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ hqC
  -- Les constantes et les degrés totaux des parties impaire et paire.
  obtain ⟨co, hco_def⟩ : ∃ c : ℂ,
      c = ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, ((betaRoots q n α i).map fun a ↦ -a).prod :=
    ⟨_, rfl⟩
  obtain ⟨ce, hce_def⟩ : ∃ c : ℂ,
      c = ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, ((betaRoots q n α i).map fun a ↦ -a).prod :=
    ⟨_, rfl⟩
  obtain ⟨A, hA_def⟩ : ∃ m : ℕ,
      m = ∑ i ∈ (Finset.range (2 * n + 1)).filter Odd, (betaRoots q n α i).card := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ m : ℕ,
      m = ∑ i ∈ (Finset.range (2 * n + 1)).filter Even, (betaRoots q n α i).card := ⟨_, rfl⟩
  have hχ : chi n P = (B : ℤ) - A := by
    rw [chi_eq hF, hA_def, hB_def]
    push_cast
    rfl
  have hco : co ^ 2 = ((q : ℂ) ^ n) ^ A := by
    rw [hco_def, hA_def]
    exact sq_prod_neg hq0 hF hB Odd (fun i hi ↦ odd_two_mul_sub_iff n hi)
  have hce : ce ^ 2 = ((q : ℂ) ^ n) ^ B := by
    rw [hce_def, hB_def]
    exact sq_prod_neg hq0 hF hB Even (fun i hi ↦ even_two_mul_sub_iff n hi)
  have hce0 : ce ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hce
    exact pow_ne_zero _ hu0 hce.symm
  have hchi : (∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) = chi n P :=
    rfl
  rw [hchi]
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = (q : ℝ) ^ ((n : ℝ) * ((chi n P : ℤ) : ℝ) / 2) := ⟨_, rfl⟩
  rw [← hr_def]
  have hr0 : (r : ℂ) ≠ 0 := by
    have : 0 < r := hr_def ▸ Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < q by omega)) _
    exact_mod_cast this.ne'
  have hr2 : (r : ℂ) ^ 2 = ((q : ℂ) ^ n) ^ chi n P := by
    have hreal : r ^ 2 = (q : ℝ) ^ ((n : ℤ) * chi n P) := by
      rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have := congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
    simp only [Complex.ofReal_pow, Complex.ofReal_zpow, Complex.ofReal_natCast] at this
    rw [this, zpow_mul, zpow_natCast]
  have hK : (co / ce * ((q : ℂ) ^ n) ^ chi n P) ^ 2 = (r : ℂ) ^ 2 := by
    rw [hr2]
    exact sq_const_eq hu0 hco hce hχ
  have hε := sq_eq_sq_iff_eq_or_eq_neg.mp hK
  refine ⟨(co / ce * ((q : ℂ) ^ n) ^ chi n P) / r, ?_, fun t ht _ _ ↦ ?_⟩
  · rcases hε with h | h
    · left; rw [h, div_self hr0]
    · right; rw [h, neg_div, div_self hr0]
  · have ho := prod_aeval_inv hq0 hF hB Odd (fun i hi ↦ odd_two_mul_sub_iff n hi) ht
    have he := prod_aeval_inv hq0 hF hB Even (fun i hi ↦ even_two_mul_sub_iff n hi) ht
    rw [← hco_def, ← hA_def] at ho
    rw [← hce_def, ← hB_def] at he
    rw [ho, he, div_mul_cancel₀ _ hr0]
    have hut : (q : ℂ) ^ n * t ≠ 0 := mul_ne_zero hu0 ht
    have hpow : ((q : ℂ) ^ n * t)⁻¹ ^ A / ((q : ℂ) ^ n * t)⁻¹ ^ B = ((q : ℂ) ^ n * t) ^ chi n P := by
      rw [inv_pow, inv_pow, inv_div_inv, hχ, zpow_sub₀ hut, zpow_natCast, zpow_natCast]
    rw [mul_div_mul_comm, mul_div_mul_comm, hpow, mul_zpow]
    ring

/-! ### Les trois conclusions et l'assemblage -/

variable (n) in
/-- `Z · ∏_{pair} P_i = ∏_{impair} P_i`. -/
def ZetaFactConcl (Z : PowerSeries ℚ) (P : ℕ → ℤ[X]) : Prop :=
  Z * (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
      ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)

variable (n) in
/-- Les `P_i` (`1 ≤ i ≤ 2n - 1`) se factorisent par les `α_i`, non nuls. -/
def FactorConcl (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
    (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
    ∀ a ∈ α i, a ≠ 0

variable (q n) in
/-- L'équation fonctionnelle sur les valeurs (clause de `weil_conjectures` et de FE). -/
def FunEqConcl (P : ℕ → ℤ[X]) : Prop :=
  ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
    ∀ t : ℂ, t ≠ 0 →
      (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, aeval t (P i)) ≠ 0 →
      (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
          aeval (((q : ℂ) ^ n * t)⁻¹) (P i)) ≠ 0 →
      (∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            aeval (((q : ℂ) ^ n * t)⁻¹) (P i)) /
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            aeval (((q : ℂ) ^ n * t)⁻¹) (P i)) =
        ε * (((q : ℝ) ^ ((n : ℝ) *
            ((∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ) : ℤ) : ℝ)
              / 2) : ℝ) : ℂ) *
          t ^ (∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) *
          ((∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, aeval t (P i)) /
            (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, aeval t (P i)))

variable (q n) in
def AlphaSymmConcl (α : ℕ → Multiset ℂ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 2 * n - 1 → α (2 * n - i) = (α i).map fun a => (q : ℂ) ^ n / a

variable (q n) in
def WeightConcl (α : ℕ → Multiset ℂ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 2 * n - 1 → ∀ a ∈ α i, ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2)

variable (q n) in
/-- Conclusion de `riemann_hypothesis` (même imbrication des conjonctions que l'énoncé). -/
def RHConcl (Z : PowerSeries ℚ) (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ) : Prop :=
  ZetaFactConcl n Z P ∧ P 0 = 1 - Polynomial.X ∧ P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
    FactorConcl n P α ∧ WeightConcl q n α

variable (q n) in
/-- Conclusion de `rationality_functional_equation`. -/
def FEConcl (Z : PowerSeries ℚ) (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ) : Prop :=
  ZetaFactConcl n Z P ∧ P 0 = 1 - Polynomial.X ∧ P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
    FactorConcl n P α ∧ FunEqConcl q n P ∧ AlphaSymmConcl q n α

variable (q n) in
/-- Conclusion de `weil_conjectures`. -/
def WeilConcl (Z : PowerSeries ℚ) (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ) : Prop :=
  ZetaFactConcl n Z P ∧ P 0 = 1 - Polynomial.X ∧ P (2 * n) = 1 - C ((q : ℤ) ^ n) * Polynomial.X ∧
    FactorConcl n P α ∧ FunEqConcl q n P ∧ AlphaSymmConcl q n α ∧ WeightConcl q n α

/-- **FE ⇒ diviseur de `Z` symétrique.** -/
theorem zetaDivisorSymm_of_fe (hq : q ≠ 0) {Z : PowerSeries ℚ} {P : ℕ → ℤ[X]}
    {α : ℕ → Multiset ℂ} (h : FEConcl q n Z P α) : ZetaDivisorSymm q n Z := by
  obtain ⟨hZ, h0, h2n, hfac, -, hsym⟩ := h
  exact zetaDivisorSymm_of_betaSymm hq (factors_of q n hq P α h0 h2n hfac) hZ
    (betaSymm_of_alphaSymm hq α hsym)

/-- **Lemme W.** RH et la symétrie du diviseur de `Z` donnent la conclusion de
`weil_conjectures`, avec les mêmes `P` et `α`. -/
theorem weil_of_rh_of_zetaDivisorSymm (hq : 1 < q) {Z : PowerSeries ℚ} {P : ℕ → ℤ[X]}
    {α : ℕ → Multiset ℂ} (h : RHConcl q n Z P α) (hsym : ZetaDivisorSymm q n Z) :
    WeilConcl q n Z P α := by
  have hq0 : q ≠ 0 := by omega
  obtain ⟨hZ, h0, h2n, hfac, hw⟩ := h
  have hF := factors_of q n hq0 P α h0 h2n hfac
  have hD := divisorSymm_of_zetaDivisorSymm hq0 hF hZ hsym
  have hB := betaSymm_of_weights hq α hw hD
  refine ⟨hZ, h0, h2n, hfac, functional_equation_of_betaSymm hq hF hB, ?_, hw⟩
  intro i h1 h2
  have := hB (2 * n - i) (by omega)
  rwa [betaRoots_of_mid q n α (by omega) (by omega), show 2 * n - (2 * n - i) = i by omega,
    betaRoots_of_mid q n α h1 h2] at this

/-- **Réduction du but de la mission** : RH et FE donnent la conclusion de `weil_conjectures`. -/
theorem weil_of_rh_of_fe (hq : 1 < q) {Z : PowerSeries ℚ}
    (hRH : ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), RHConcl q n Z P α)
    (hFE : ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), FEConcl q n Z P α) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), WeilConcl q n Z P α := by
  obtain ⟨P, α, h⟩ := hRH
  obtain ⟨P', α', h'⟩ := hFE
  exact ⟨P, α, weil_of_rh_of_zetaDivisorSymm hq h (zetaDivisorSymm_of_fe (by omega) h')⟩

end Assembly

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/FunctionalEquationSplit.lean` -/

section

/-!
# Découpage artificiel de l'équation fonctionnelle (partie N4c)

Pour `n ≥ 2`, la conclusion de `rationality_functional_equation` ne demande, au-delà de la
présentation entière `Z · B = A` (N2e), que la **symétrie du diviseur** de `Z` sous
`σ : a ↦ qⁿ / a` (`ZetaDivisorSymm`). On répartit artificiellement `A` et `B` entre les `P_i` :
avec `X₀ = (1 - X)(1 - qⁿX)`, on pose `P_n = A X₀ B`, `P_{n±1} = A X₀` (`n` pair) ou `B`
(`n` impair), et `P_i = 1` ailleurs (`1 ≤ i ≤ 2n - 1`) ; le quotient `∏_{impair} / ∏_{pair}` vaut
`A / B` dans les deux cas.

Étapes :
1. une présentation première entre elles a des racines inverses disjointes ;
2. le diviseur `ρ(A) - ρ(B)` étant symétrique, `ρ(A)` et `ρ(B)` sont alors **chacun** stables
   par `σ` ;
3. construction des `P_i` et `α_i = ρ(P_i)`, et conclusion `FEConcl` (l'équation fonctionnelle
   sur les valeurs vient de `functional_equation_of_betaSymm`).

Plan : `docs/inventaire_N4.md` §1.4 et §5.1.
-/

open Polynomial

namespace WeilConjectures.Bridge

section Split

open Classical

variable {q n : ℕ}

/-! ### Étape 1 : racines inverses disjointes -/

theorem map_complex_coeff_zero {A : ℤ[X]} (hA : A.coeff 0 = 1) :
    (A.map (Int.castRingHom ℂ)).coeff 0 = 1 := by
  simp [coeff_map, hA]

/-- `a ∈ ρ(A)` signifie que `a⁻¹` est racine de `A` (sur `ℂ`). -/
theorem isRoot_inv_of_mem_invRoots {A : ℤ[X]} (hA : A.coeff 0 = 1) {a : ℂ}
    (ha : a ∈ invRoots A) : (A.map (Int.castRingHom ℂ)).IsRoot a⁻¹ := by
  have h := roots_eq_map_inv_roots_reverse (map_complex_coeff_zero hA)
  have hmem : a⁻¹ ∈ (A.map (Int.castRingHom ℂ)).roots := by
    rw [h]
    exact Multiset.mem_map_of_mem _ ha
  exact (mem_roots (map_ne_zero_of_coeff_zero hA)).mp hmem

/-- **Étape 1.** Une présentation première entre elles (sur `ℚ`) a des racines inverses
disjointes. -/
theorem invRoots_disjoint {A B : ℤ[X]} (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hcop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) {a : ℂ}
    (ha : a ∈ invRoots A) (hb : a ∈ invRoots B) : False := by
  obtain ⟨u, v, huv⟩ := hcop
  have hc : ∀ C : ℤ[X], (C.map (Int.castRingHom ℚ)).eval₂ (algebraMap ℚ ℂ) a⁻¹ =
      (C.map (Int.castRingHom ℂ)).eval a⁻¹ := fun C ↦ by
    rw [eval₂_map, eval_map]
    congr 1
  have h := congrArg (eval₂ (algebraMap ℚ ℂ) a⁻¹) huv
  rw [eval₂_add, eval₂_mul, eval₂_mul, hc, hc, isRoot_inv_of_mem_invRoots hA ha,
    isRoot_inv_of_mem_invRoots hB hb, eval₂_one] at h
  simp at h

/-! ### Étape 2 : chaque partie du diviseur est stable -/

/-- **Étape 2 (comptage).** Si `σ` est une involution, `a` et `b` disjoints et
`σ(a) + b = a + σ(b)`, alors `σ(a) = a` et `σ(b) = b`. -/
theorem map_eq_of_disjoint {σ : ℂ → ℂ} (hσ : Function.Involutive σ) {a b : Multiset ℂ}
    (hdis : ∀ x, x ∈ a → x ∈ b → False) (h : a.map σ + b = a + b.map σ) :
    a.map σ = a ∧ b.map σ = b := by
  have key : ∀ (s : Multiset ℂ) (y : ℂ), (s.map σ).count y = s.count (σ y) := fun s y ↦ by
    conv_lhs => rw [← hσ y]
    exact Multiset.count_map_eq_count' σ s hσ.injective (σ y)
  have hd : ∀ x, a.count x = 0 ∨ b.count x = 0 := fun x ↦ by
    by_cases hx : x ∈ a
    · exact .inr (Multiset.count_eq_zero.mpr fun hb ↦ hdis x hx hb)
    · exact .inl (Multiset.count_eq_zero.mpr hx)
  have hcount : ∀ x, a.count (σ x) = a.count x ∧ b.count (σ x) = b.count x := fun x ↦ by
    have e := congrArg (Multiset.count x) h
    simp only [Multiset.count_add, key] at e
    have h1 := hd x
    have h2 := hd (σ x)
    omega
  constructor <;> ext x <;> rw [key]
  · exact (hcount x).1
  · exact (hcount x).2

/-- **Étape 2.** Pour une présentation première entre elles `Z · B = A` et un diviseur de `Z`
symétrique, `ρ(A)` et `ρ(B)` sont chacun stables par `σ`. -/
theorem invRoots_stable (hq : q ≠ 0) {Z : PowerSeries ℚ} {A B : ℤ[X]} (hA : A.coeff 0 = 1)
    (hB : B.coeff 0 = 1)
    (hcop : IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (hZ : Z * toSeries B = toSeries A) (hsym : ZetaDivisorSymm q n Z) :
    (invRoots A).map (reflectRoot q n) = invRoots A ∧
      (invRoots B).map (reflectRoot q n) = invRoots B := by
  obtain ⟨A', B', hA', hB', hZ', hs'⟩ := hsym
  have hc := invRoots_cross hA' hB' hA hB hZ' hZ
  have hs := divisor_transfer (reflectRoot_reflectRoot q n hq) hs' hc
  exact map_eq_of_disjoint (reflectRoot_reflectRoot q n hq)
    (fun x ha hb ↦ invRoots_disjoint hA hB hcop ha hb) hs

/-! ### Étape 3 : construction des `P_i` -/

variable (q n) in
/-- `X₀ = (1 - X)(1 - qⁿX)`, de racines inverses `{1, qⁿ}`. -/
noncomputable def edgePoly : ℤ[X] := (1 - X) * (1 - C ((q : ℤ) ^ n) * X)

variable (q n) in
/-- `P_{n±1}` : `A X₀` si `n` est pair (indices `n ± 1` impairs), `B` sinon. -/
noncomputable def sidePoly (A B : ℤ[X]) : ℤ[X] := if Even n then A * edgePoly q n else B

variable (q n) in
/-- Les `P_i` du découpage artificiel. -/
noncomputable def splitPoly (A B : ℤ[X]) (i : ℕ) : ℤ[X] :=
  if i = 0 then 1 - X
  else if i = 2 * n then 1 - C ((q : ℤ) ^ n) * X
  else if i = n then A * edgePoly q n * B
  else if i + 1 = n ∨ i = n + 1 then sidePoly q n A B
  else 1

variable (q n) in
/-- Les `α_i = ρ(P_i)`. -/
noncomputable def splitRoots (A B : ℤ[X]) (i : ℕ) : Multiset ℂ := invRoots (splitPoly q n A B i)

section Values

variable {A B : ℤ[X]}

theorem splitPoly_zero : splitPoly q n A B 0 = 1 - X := by simp [splitPoly]

theorem splitPoly_two_mul (hn : 2 ≤ n) :
    splitPoly q n A B (2 * n) = 1 - C ((q : ℤ) ^ n) * X := by
  rw [splitPoly, if_neg (by omega), if_pos rfl]

theorem splitPoly_self (hn : 2 ≤ n) : splitPoly q n A B n = A * edgePoly q n * B := by
  rw [splitPoly, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem splitPoly_pred (hn : 2 ≤ n) : splitPoly q n A B (n - 1) = sidePoly q n A B := by
  rw [splitPoly, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem splitPoly_succ (hn : 2 ≤ n) : splitPoly q n A B (n + 1) = sidePoly q n A B := by
  rw [splitPoly, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem splitPoly_of_ne {i : ℕ} (h0 : i ≠ 0) (h2n : i ≠ 2 * n) (hn : i ≠ n) (hp : i + 1 ≠ n)
    (hs : i ≠ n + 1) : splitPoly q n A B i = 1 := by
  rw [splitPoly, if_neg h0, if_neg h2n, if_neg hn, if_neg (by omega)]

/-- La répartition est symétrique : `P_{2n-i} = P_i` pour `1 ≤ i ≤ 2n - 1`. -/
theorem splitPoly_reflect {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 2 * n - 1) :
    splitPoly q n A B (2 * n - i) = splitPoly q n A B i := by
  unfold splitPoly
  split_ifs <;> first | rfl | omega

theorem edgePoly_coeff_zero : (edgePoly q n).coeff 0 = 1 := by
  simp [edgePoly, coeff_zero_eq_eval_zero]

theorem splitPoly_coeff_zero (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1) (i : ℕ) :
    (splitPoly q n A B i).coeff 0 = 1 := by
  have hA' : A.eval 0 = 1 := by rwa [← coeff_zero_eq_eval_zero]
  have hB' : B.eval 0 = 1 := by rwa [← coeff_zero_eq_eval_zero]
  have hE : (edgePoly q n).eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero, edgePoly_coeff_zero]
  unfold splitPoly sidePoly
  split_ifs <;> simp [coeff_zero_eq_eval_zero, hA', hB', hE]

end Values

/-! #### Les produits pairs et impairs -/

section Products

variable {A B : ℤ[X]}

/-- Le produit ne voit que les indices où `P_i ≠ 1`. -/
theorem prod_splitPoly_eq (S : ℕ → Prop) [DecidablePred S] (T : Finset ℕ)
    (hT : T ⊆ (Finset.range (2 * n + 1)).filter S)
    (h1 : ∀ i ∈ (Finset.range (2 * n + 1)).filter S, i ∉ T → splitPoly q n A B i = 1) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter S, splitPoly q n A B i =
      ∏ i ∈ T, splitPoly q n A B i :=
  (Finset.prod_subset hT h1).symm

theorem prod_even_of_even (hn : 2 ≤ n) (he : Even n) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, splitPoly q n A B i =
      edgePoly q n * (A * edgePoly q n * B) := by
  obtain ⟨r, hr⟩ := he
  rw [prod_splitPoly_eq Even {0, n, 2 * n}]
  · rw [Finset.prod_insert (by simp; omega), Finset.prod_pair (by omega), splitPoly_zero,
      splitPoly_self hn, splitPoly_two_mul hn, edgePoly]
    ring
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hi with rfl | rfl | rfl
    · exact ⟨by omega, 0, rfl⟩
    · exact ⟨by omega, r, hr⟩
    · exact ⟨by omega, even_two_mul n⟩
  · intro i hi hiT
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hiT
    obtain ⟨-, s, hs⟩ := hi
    exact splitPoly_of_ne hiT.1 hiT.2.2 hiT.2.1 (by omega) (by omega)

theorem prod_odd_of_even (hn : 2 ≤ n) (he : Even n) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, splitPoly q n A B i =
      (A * edgePoly q n) * (A * edgePoly q n) := by
  obtain ⟨r, hr⟩ := he
  rw [prod_splitPoly_eq Odd {n - 1, n + 1}]
  · rw [Finset.prod_pair (by omega), splitPoly_pred hn, splitPoly_succ hn, sidePoly,
      if_pos ⟨r, hr⟩]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hi with rfl | rfl
    · exact ⟨by omega, r - 1, by omega⟩
    · exact ⟨by omega, r, by omega⟩
  · intro i hi hiT
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hiT
    obtain ⟨-, s, hs⟩ := hi
    exact splitPoly_of_ne (by omega) (by omega) (by omega) (by omega) hiT.2

theorem prod_even_of_odd (hn : 2 ≤ n) (ho : ¬Even n) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, splitPoly q n A B i =
      edgePoly q n * (B * B) := by
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp ho
  rw [prod_splitPoly_eq Even {0, n - 1, n + 1, 2 * n}]
  · rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_pair (by omega), splitPoly_zero, splitPoly_pred hn, splitPoly_succ hn,
      splitPoly_two_mul hn, sidePoly, if_neg ho, edgePoly]
    ring
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨by omega, 0, rfl⟩
    · exact ⟨by omega, r, by omega⟩
    · exact ⟨by omega, r + 1, by omega⟩
    · exact ⟨by omega, even_two_mul n⟩
  · intro i hi hiT
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hiT
    obtain ⟨-, s, hs⟩ := hi
    exact splitPoly_of_ne hiT.1 hiT.2.2.2 (by omega) (by omega) hiT.2.2.1

theorem prod_odd_of_odd (hn : 2 ≤ n) (ho : ¬Even n) :
    ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, splitPoly q n A B i =
      A * edgePoly q n * B := by
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp ho
  rw [prod_splitPoly_eq Odd {n}]
  · rw [Finset.prod_singleton, splitPoly_self hn]
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, r, hr⟩
  · intro i hi hiT
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_singleton] at hiT
    obtain ⟨-, s, hs⟩ := hi
    exact splitPoly_of_ne (by omega) (by omega) hiT (by omega) (by omega)

/-- `Z · ∏_{pair} P_i = ∏_{impair} P_i`. -/
theorem zetaFactConcl_split (hn : 2 ≤ n) {Z : PowerSeries ℚ} (hZ : Z * toSeries B = toSeries A) :
    ZetaFactConcl n Z (splitPoly q n A B) := by
  unfold ZetaFactConcl
  change Z * ∏ i ∈ _, toSeries (splitPoly q n A B i) = ∏ i ∈ _, toSeries (splitPoly q n A B i)
  rw [← toSeries_prod, ← toSeries_prod]
  by_cases he : Even n
  · rw [prod_even_of_even hn he, prod_odd_of_even hn he]
    simp only [toSeries_mul]
    linear_combination (toSeries (edgePoly q n) * toSeries A * toSeries (edgePoly q n)) * hZ
  · rw [prod_even_of_odd hn he, prod_odd_of_odd hn he]
    simp only [toSeries_mul]
    linear_combination (toSeries (edgePoly q n) * toSeries B) * hZ

end Products

/-! #### Les `α_i` : factorisation et symétrie -/

section Roots

variable {A B : ℤ[X]}

/-- `ρ(1 - cX) = {c}` pour `c ≠ 0`. -/
theorem invRoots_one_sub_C_mul_X {c : ℤ} (hc : c ≠ 0) : invRoots (1 - C c * X) = {(c : ℂ)} := by
  unfold invRoots
  apply reverse_roots_of_prod
  · simp
  · simpa using hc

/-- `ρ(X₀) = {1, qⁿ}`. -/
theorem invRoots_edgePoly (hq : q ≠ 0) : invRoots (edgePoly q n) = {1} + {(q : ℂ) ^ n} := by
  have h1 : (1 - X : ℤ[X]) = 1 - C 1 * X := by simp
  have hqn : ((q : ℤ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq)
  rw [edgePoly, invRoots_mul (by simp) (by simp), h1, invRoots_one_sub_C_mul_X one_ne_zero,
    invRoots_one_sub_C_mul_X hqn]
  push_cast
  rfl

theorem invRoots_one : invRoots (1 : ℤ[X]) = 0 := by
  simp [invRoots, reverse_one']

theorem map_reflect_edge (hq : q ≠ 0) :
    (invRoots (edgePoly q n)).map (reflectRoot q n) = invRoots (edgePoly q n) := by
  have hqn : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq)
  rw [invRoots_edgePoly hq, Multiset.map_add, Multiset.map_singleton, Multiset.map_singleton,
    reflectRoot, reflectRoot, div_one, div_self hqn, add_comm]

/-- Chaque `α_i` (`1 ≤ i ≤ 2n - 1`) est stable par `σ`. -/
theorem map_reflect_splitRoots (hq : q ≠ 0) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hsA : (invRoots A).map (reflectRoot q n) = invRoots A)
    (hsB : (invRoots B).map (reflectRoot q n) = invRoots B) (i : ℕ) :
    (splitRoots q n A B i).map (reflectRoot q n) = splitRoots q n A B i ∨ i = 0 ∨
      i = 2 * n := by
  have hAE : (A * edgePoly q n).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero,
      hA, edgePoly_coeff_zero, one_mul]
  have hE := map_reflect_edge (n := n) hq
  have hAE' : (invRoots (A * edgePoly q n)).map (reflectRoot q n) =
      invRoots (A * edgePoly q n) := by
    rw [invRoots_mul hA edgePoly_coeff_zero, Multiset.map_add, hsA, hE]
  unfold splitRoots splitPoly
  split_ifs with h0 h2n hn hs
  · exact .inr (.inl h0)
  · exact .inr (.inr h2n)
  · left
    rw [invRoots_mul hAE hB, Multiset.map_add, hAE', hsB]
  · left
    unfold sidePoly
    split_ifs
    · exact hAE'
    · exact hsB
  · left
    rw [invRoots_one, Multiset.map_zero]

end Roots

/-! ### Conclusion -/

/-- **N4c.** Pour `n ≥ 2`, une présentation entière première entre elles de `Z` (celle de N2e) et
la symétrie de son diviseur donnent la conclusion de `rationality_functional_equation`. -/
theorem fe_of_presentation (hq : 1 < q) (hn : 2 ≤ n) {Z : PowerSeries ℚ}
    (hpres : ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      Z * toSeries B = toSeries A)
    (hsym : ZetaDivisorSymm q n Z) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), FEConcl q n Z P α := by
  have hq0 : q ≠ 0 := by omega
  obtain ⟨A, B, hA, hB, hcop, hZ⟩ := hpres
  obtain ⟨hsA, hsB⟩ := invRoots_stable hq0 hA hB hcop hZ hsym
  have h0 := splitPoly_zero (q := q) (n := n) (A := A) (B := B)
  have h2n := splitPoly_two_mul (q := q) (A := A) (B := B) hn
  have hfac : FactorConcl n (splitPoly q n A B) (splitRoots q n A B) := by
    intro i _ _
    have hc := map_complex_coeff_zero (splitPoly_coeff_zero (q := q) (n := n) hA hB i)
    exact ⟨eq_prod_one_sub_C_mul_X hc, fun a ha ↦
      ne_zero_of_mem_roots_reverse (map_ne_zero_of_coeff_zero
        (splitPoly_coeff_zero (q := q) (n := n) hA hB i)) ha⟩
  have hα : ∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
      splitRoots q n A B (2 * n - i) = (splitRoots q n A B i).map (reflectRoot q n) := by
    intro i h1 h2
    rcases map_reflect_splitRoots hq0 hA hB hsA hsB i with h | h | h
    · rw [h, splitRoots, splitRoots, splitPoly_reflect h1 h2]
    · omega
    · omega
  have hF := factors_of q n hq0 _ _ h0 h2n hfac
  have hBS := betaSymm_of_alphaSymm hq0 _ hα
  exact ⟨splitPoly q n A B, splitRoots q n A B, zetaFactConcl_split hn hZ, h0, h2n, hfac,
    functional_equation_of_betaSymm hq hF hBS, hα⟩

/-! ### Étape (i) : la forme sans racines de N4a

L'énoncé N4a (`docs/inventaire_N4.md` §1.6) évite `ℂ` : avec `Q = qⁿX`,
`A.reverse(Q) · B = c · A · B.reverse(Q)` dans `ℚ[X]`, c'est-à-dire
`Z(1/(qⁿt)) = c (qⁿt)^{deg B - deg A} Z(t)`. Ses racines sur `ℂ` donnent `ZetaDivisorSymm` : celles
de `A.reverse(Q)` sont les `a / qⁿ = σ(a)⁻¹`, `a ∈ ρ(A)`, et celles de `A` les `a⁻¹`. -/

variable (q n) in
/-- **Conclusion de N4a** (forme sans racines) : `Z = A / B`, `A(0) = B(0) = 1`, et
`A.reverse(qⁿX) · B = c · A · B.reverse(qⁿX)` pour un `c ∈ ℚ` non nul. -/
def ZetaFunEqConcl (Z : PowerSeries ℚ) : Prop :=
  ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧ Z * toSeries B = toSeries A ∧
    ∃ c : ℚ, c ≠ 0 ∧
      ((A.reverse.comp (C ((q : ℤ) ^ n) * X)) * B).map (Int.castRingHom ℚ) =
        C c * (A * (B.reverse.comp (C ((q : ℤ) ^ n) * X))).map (Int.castRingHom ℚ)

/-- Les racines de `(∏ (X - a)) (cX)` sont les `a / c`. -/
theorem roots_prod_comp_C_mul_X {c : ℂ} (hc : c ≠ 0) (s : Multiset ℂ) :
    (((s.map fun a ↦ X - C a).prod).comp (C c * X)).roots = s.map (c⁻¹ * ·) := by
  have hlin : ∀ a : ℂ, (X - C a).comp (C c * X) = C c * X - C a := fun a ↦ by
    simp [sub_comp]
  rw [multiset_prod_comp, Multiset.map_map, roots_multiset_prod]
  · rw [Multiset.bind_map]
    refine (Multiset.bind_congr fun a _ ↦ ?_).trans (Multiset.bind_singleton _ _)
    rw [Function.comp_apply, hlin, roots_C_mul_X_sub_C _ hc]
  · rw [Multiset.mem_map]
    rintro ⟨a, _, h⟩
    rw [Function.comp_apply, hlin] at h
    have := congrArg (coeff · 1) h
    simp [coeff_C] at this
    exact hc this

/-- `ρ(A)` sont les racines de `A.reverse` sur `ℂ`, qui est unitaire et scindé. -/
theorem reverse_map_eq_prod {A : ℤ[X]} (hA : A.coeff 0 = 1) :
    (A.map (Int.castRingHom ℂ)).reverse = ((invRoots A).map fun a ↦ X - C a).prod :=
  (prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (monic_reverse_of_coeff_zero_eq_one (map_complex_coeff_zero hA))
    IsAlgClosed.card_roots_eq_natDegree).symm

/-- Les racines de `A.reverse(qⁿX)` sur `ℂ` sont les `a / qⁿ`, `a ∈ ρ(A)`. -/
theorem roots_reverse_comp (hq : q ≠ 0) {A : ℤ[X]} (hA : A.coeff 0 = 1) :
    ((A.reverse.comp (C ((q : ℤ) ^ n) * X)).map (Int.castRingHom ℂ)).roots =
      (invRoots A).map (((q : ℂ) ^ n)⁻¹ * ·) := by
  have hQ : (C ((q : ℤ) ^ n) * X).map (Int.castRingHom ℂ) = C ((q : ℂ) ^ n) * X := by simp
  rw [Polynomial.map_comp, ← reverse_map_of_injective _ (RingHom.injective_int _),
    reverse_map_eq_prod hA, hQ, roots_prod_comp_C_mul_X (pow_ne_zero _ (by exact_mod_cast hq))]

theorem map_ne_zero_of_coeff_zero_ne {P : ℤ[X]} (h : P.coeff 0 ≠ 0) :
    P.map (Int.castRingHom ℂ) ≠ 0 := fun h' ↦ h (by
  have := congrArg (coeff · 0) h'
  simpa [coeff_map] using this)

theorem reverse_comp_coeff_zero_ne {A : ℤ[X]} (hA : A.coeff 0 = 1) :
    (A.reverse.comp (C ((q : ℤ) ^ n) * X)).coeff 0 ≠ 0 := by
  have hA0 : A ≠ 0 := fun h ↦ by simp [h] at hA
  rw [coeff_zero_eq_eval_zero, eval_comp]
  simpa [← coeff_zero_eq_eval_zero, coeff_zero_reverse] using hA0

/-- **N4a ⇒ diviseur de `Z` symétrique.** -/
theorem zetaDivisorSymm_of_funEq (hq : q ≠ 0) {Z : PowerSeries ℚ} (h : ZetaFunEqConcl q n Z) :
    ZetaDivisorSymm q n Z := by
  obtain ⟨A, B, hA, hB, hZ, c, hc, hid⟩ := h
  refine ⟨A, B, hA, hB, hZ, ?_⟩
  have hC := congrArg (Polynomial.map (algebraMap ℚ ℂ)) hid
  have hint : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hint] at hC
  have hr := congrArg roots hC
  have hc' : algebraMap ℚ ℂ c ≠ 0 := by simpa using hc
  rw [roots_mul (mul_ne_zero (map_ne_zero_of_coeff_zero_ne (reverse_comp_coeff_zero_ne hA))
      (map_ne_zero_of_coeff_zero hB)), roots_C_mul _ hc',
    roots_mul (mul_ne_zero (map_ne_zero_of_coeff_zero hA)
      (map_ne_zero_of_coeff_zero_ne (reverse_comp_coeff_zero_ne hB))),
    roots_reverse_comp hq hA, roots_reverse_comp hq hB,
    roots_eq_map_inv_roots_reverse (map_complex_coeff_zero hA),
    roots_eq_map_inv_roots_reverse (map_complex_coeff_zero hB)] at hr
  have hinv := congrArg (Multiset.map (·⁻¹)) hr
  simp only [Multiset.map_add, Multiset.map_map] at hinv
  have e1 : ∀ s : Multiset ℂ, s.map ((·⁻¹) ∘ (((q : ℂ) ^ n)⁻¹ * ·)) = s.map (reflectRoot q n) :=
    fun s ↦ Multiset.map_congr rfl fun a _ ↦ by
      simp [reflectRoot, div_eq_mul_inv, mul_comm]
  have e2 : ∀ s : Multiset ℂ, s.map ((·⁻¹) ∘ (·⁻¹)) = s := fun s ↦ by
    conv_rhs => rw [← Multiset.map_id s]
    exact Multiset.map_congr rfl fun a _ ↦ inv_inv a
  rw [e1, e1, e2, e2] at hinv
  exact hinv

/-- **N4c, avec N4a.** Pour `n ≥ 2`, la présentation de N2e et la conclusion de N4a donnent celle
de `rationality_functional_equation`. -/
theorem fe_of_presentation_of_funEq (hq : 1 < q) (hn : 2 ≤ n) {Z : PowerSeries ℚ}
    (hpres : ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      Z * toSeries B = toSeries A)
    (hfe : ZetaFunEqConcl q n Z) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), FEConcl q n Z P α :=
  fe_of_presentation hq hn hpres (zetaDivisorSymm_of_funEq (by omega) hfe)

end Split

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/Points.lean` -/

section

/-!
# Comptage de points de la plateforme (partie A1 du pont)

Dépliage de `pointCount` : en degré `m ≥ 1`, c'est le nombre de `k`-morphismes
`Spec 𝔽_{q^m} ⟶ X`, avec `𝔽_{q^m} = FiniteField.Extension k p m` ; en degré `0`, c'est `0`.

Dans `finite_fields`, `pointCount X π n` compte les points sur `Extension k p n`, qui y désigne
`FiniteField.Extension k p (n + 1)` : il correspond à `pointCount p f (n + 1)` ci-dessous
(`pointCount_succ`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k] [CharP k p]
  {X : Scheme} (f : X ⟶ Spec (.of k))

@[simp]
theorem pointCount_zero : pointCount p f 0 = 0 := by
  simp [pointCount]

/-- En degré `m ≠ 0`, `pointCount` compte les points sur l'extension de degré `m`. -/
theorem pointCount_of_neZero (m : ℕ) [NeZero m] :
    pointCount p f m = pointsOver f (FiniteField.Extension k p m) := by
  rw [pointCount, dif_neg (NeZero.ne m)]

/-- Version indexée comme dans `finite_fields` (degré `n + 1`). -/
theorem pointCount_succ (n : ℕ) :
    pointCount p f (n + 1) = pointsOver f (FiniteField.Extension k p (n + 1)) :=
  pointCount_of_neZero p f (n + 1)

theorem zetaFunction_eq : zetaFunction p f = zetaOfCounts (pointCount p f) := rfl

end WeilConjectures.Bridge

end
end

/-! ## Recopié de `Bridge/ProjectiveProper.lean` -/

section

/-!
# Un `k`-schéma projectif est propre

`IsProjectiveOver k f` (une immersion fermée dans `ℙᴺ_k` au-dessus de `k`) entraîne `IsProper f` :
`ℙᴺ_k ⟶ Spec k` est `Proj ⟶ Spec 𝒜₀`, propre, suivi de `Spec` de la surjection `k → 𝒜₀`, finie.
Sert aux courbes (partie C1) comme à la rationalité (N1a).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

attribute [local instance] MvPolynomial.gradedAlgebra

section Proper

variable {k : Type} [Field k]

/-- Le morphisme `Spec 𝒜₀ ⟶ Spec k` est fini : `k → 𝒜₀` est surjectif, car les polynômes
homogènes de degré 0 sont les constantes. -/
theorem surjective_algebraMap_grade_zero (N : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  intro x
  have hx : (x : MvPolynomial (Fin (N + 1)) k) ∈ (1 : Submodule k _) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero]
    exact x.2
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hx
  exact ⟨y, Subtype.ext hy⟩

/-- **C1.** Un `k`-schéma projectif est propre. -/
theorem isProper_of_isProjectiveOver {X : Scheme} (f : X ⟶ Spec (.of k))
    (h : IsProjectiveOver k f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.Finite.of_surjective _ (surjective_algebraMap_grade_zero N)
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
      (MvPolynomial (Fin (N + 1)) k) :=
    haveI : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (MvPolynomial (Fin (N + 1)) k) :=
      IsScalarTower.of_algebraMap_eq (R := k)
        (S := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (A := MvPolynomial (Fin (N + 1)) k) fun _ ↦ rfl
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  unfold projectiveSpace.toSpec
  infer_instance

end Proper

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/ZetaDimZero.lean` -/

section

/-!
# Le cas `n = 0` de `rationality_functional_equation` (partie N4b)

Un `k`-schéma `X` lisse de dimension relative `0`, géométriquement irréductible et projectif est
`Spec k` :
1. lisse de dimension relative `0` = étale (Mathlib), donc localement quasi-fini ;
2. propre (projectif) et localement quasi-fini ⇒ fini (Zariski, Mathlib), donc `X` est affine ;
3. `Γ(X, 𝒪) = k` (nœud FLT `geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth`,
   Proved) ; `X` étant affine, `f : X ⟶ Spec k` est un isomorphisme.

Alors `N_m = 1` pour tout `m ≥ 1`, comme pour `ℙ⁰_k`, d'où `Z = 1 / (1 - T)` (nœud `projectiveSpace_zeta`), et la conclusion de FE pour `n = 0` en
découle (`P_0 = 1 - T`, les autres clauses étant vides ou données par `WeilAssembly`).

Plan : `docs/inventaire_N4.md` §1.5 et §5.1.
-/

set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

section DimZero

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-! ### `X ≅ Spec k` -/

/-- Un morphisme étale est localement quasi-fini. -/
theorem locallyQuasiFinite_of_etale [Etale f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have := f.etale_appLE U.2 V.2 e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Spec (.of k), U) Γ(X, V))

/-- Un `k`-schéma fini est affine. -/
theorem isAffine_of_isFinite [IsFinite f] : IsAffine X :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (Q := fun X _ _ _ ↦ IsAffine X)
    (f := f)).mp inferInstance

/-- Un schéma affine au-dessus de `Spec k` dont les sections globales sont `k` est `Spec k`. -/
theorem isIso_of_isAffine_of_bijective [IsAffine X]
    (h : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom) :
    IsIso f := by
  have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

/-- **N4b, géométrie.** Un `k`-schéma propre, lisse de dimension relative `0` et géométriquement
irréductible est `Spec k`. -/
theorem isIso_of_smoothOfRelativeDimension_zero [SmoothOfRelativeDimension 0 f]
    [GeometricallyIrreducible f] [IsProper f] : IsIso f := by
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have : IsAffine X := isAffine_of_isFinite f
  have : Nonempty X := by
    obtain ⟨x⟩ : Nonempty (Spec (.of k)) := inferInstance
    exact ⟨(f.surjective x).choose⟩
  exact isIso_of_isAffine_of_bijective f
    ((geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth f).mp inferInstance)

/-- Si `f` est un isomorphisme, `X` a exactement un `L`-point au-dessus de `k`. -/
theorem pointsOver_of_isIso [IsIso f] (L : Type) [CommRing L] [Algebra k L] :
    pointsOver f L = 1 := by
  unfold pointsOver
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b ↦ Subtype.ext ?_⟩,
    ⟨⟨Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ inv f, by simp⟩⟩⟩
  rw [← cancel_mono f, a.2, b.2]

/-! ### La fonction zêta et la conclusion de FE -/

variable (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]

/-- **N4b, comptage.** `Z = 1 / (1 - T)`. Les comptages sont ceux de `ℙ⁰_k` (un point en chaque
degré), dont la fonction zêta est donnée par le nœud `projectiveSpace_zeta`. -/
theorem zetaFunction_mul_one_sub_of_isIso [IsIso f] :
    zetaFunction p f * (1 - PowerSeries.X) = 1 := by
  obtain ⟨hc, hz⟩ := projectiveSpace_zeta p k 0
  have h : pointCount p f = pointCount p (projectiveSpace.toSpec k 0) := by
    funext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : NeZero m := ⟨by omega⟩
      rw [hc m hm, pointCount_of_neZero, pointsOver_of_isIso]
      simp
  rw [zetaFunction_eq, h, ← zetaFunction_eq]
  simpa using hz

/-- La conclusion de `rationality_functional_equation` pour `n = 0` découle de `Z (1 - T) = 1`. -/
theorem feConcl_zero (q : ℕ) (hq : 1 < q) {Z : PowerSeries ℚ} (hZ : Z * (1 - PowerSeries.X) = 1) :
    FEConcl q 0 Z (fun _ ↦ 1 - Polynomial.X) (fun _ ↦ 0) := by
  have hq0 : q ≠ 0 := by omega
  have h0 : (fun _ ↦ 1 - Polynomial.X : ℕ → Polynomial ℤ) 0 = 1 - Polynomial.X := rfl
  have h2n : (fun _ ↦ 1 - Polynomial.X : ℕ → Polynomial ℤ) (2 * 0) =
      1 - Polynomial.C ((q : ℤ) ^ 0) * Polynomial.X := by simp
  have hfac : FactorConcl 0 (fun _ ↦ 1 - Polynomial.X) (fun _ ↦ (0 : Multiset ℂ)) :=
    fun i h1 h2 ↦ absurd h2 (by omega)
  have hα : ∀ i, 1 ≤ i → i ≤ 2 * 0 - 1 →
      (fun _ ↦ (0 : Multiset ℂ)) (2 * 0 - i) =
        ((fun _ ↦ (0 : Multiset ℂ)) i).map (reflectRoot q 0) := fun i h1 h2 ↦ absurd h2 (by omega)
  have hF := factors_of q 0 hq0 _ _ h0 h2n hfac
  refine ⟨?_, h0, h2n, hfac, functional_equation_of_betaSymm hq hF (betaSymm_of_alphaSymm hq0 _ hα),
    hα⟩
  unfold ZetaFactConcl
  have he : (Finset.range (2 * 0 + 1)).filter Even = {0} := by decide
  have ho : (Finset.range (2 * 0 + 1)).filter Odd = ∅ := by decide
  rw [he, ho, Finset.prod_singleton, Finset.prod_empty]
  simpa using hZ

/-- **N4b.** Le cas `n = 0` de `rationality_functional_equation`. -/
theorem fe_dim_zero [SmoothOfRelativeDimension 0 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → Polynomial ℤ) (α : ℕ → Multiset ℂ),
      FEConcl (Nat.card k) 0 (zetaFunction p f) P α := by
  have : IsProper f := isProper_of_isProjectiveOver f hproj
  have : IsIso f := isIso_of_smoothOfRelativeDimension_zero f
  exact ⟨_, _, feConcl_zero (Nat.card k) Finite.one_lt_card
    (zetaFunction_mul_one_sub_of_isIso f p)⟩

end DimZero

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/FEReduction.lean` -/

section

/-!
# Réduction de `rationality_functional_equation` (partie N4d)

Selon la dimension `n` :
- `n = 0` : `X ≅ Spec k` (N4b, `fe_dim_zero`) ;
- `n = 1` : le nœud `weil_conjectures_curves` (Proved), sans sa clause des poids ;
- `n ≥ 2` : le découpage artificiel (N4c, `fe_of_presentation_of_funEq`) appliqué à la
  présentation entière de N2e (`zetaFunction_integral_presentation`, Proved) et à l'équation
  fonctionnelle sans racines, nœud N4a `FiniteFields.zeta_functional_equation` (Open).

Plan : `docs/inventaire_N4.md` §5.1.
-/

open AlgebraicGeometry CategoryTheory Polynomial

namespace WeilConjectures.Bridge

/-- Le cas `n = 1` : `weil_conjectures_curves` sans la clause des poids. -/
theorem fe_curves (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), FEConcl (Nat.card k) 1 (zetaFunction p f) P α := by
  obtain ⟨P, α, hZ, h0, h2, hfac, hfe, hsym, -⟩ :=
    WeilConjectures.weil_conjectures_curves p k X f hproj
  refine ⟨P, α, hZ, h0, h2, hfac, ?_, hsym⟩
  -- `weil_conjectures_curves` écrit `(1 : ℝ)` là où `FunEqConcl` écrit `((1 : ℕ) : ℝ)`.
  simpa only [FunEqConcl, Nat.cast_one] using hfe

/-- La conclusion de FE, pour toute dimension. -/
theorem feConcl_proof (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), FEConcl (Nat.card k) n (zetaFunction p f) P α := by
  rcases n with _ | _ | n
  · exact fe_dim_zero f p hproj
  · exact fe_curves p k X f hproj
  · exact fe_of_presentation_of_funEq Finite.one_lt_card (by omega)
      (FiniteFields.zetaFunction_integral_presentation p k X f hproj)
      (FiniteFields.zeta_functional_equation p k (n + 2) X f hproj)

/-- **`rationality_functional_equation`**, à partir de `weil_conjectures_curves`, de N2e et du
nœud N4a. -/
theorem rationality_functional_equation_proof (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [Finite k] [CharP k p] (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ), FEConcl (Nat.card k) n (zetaFunction p f) P α :=
  feConcl_proof p k n X f hproj

end WeilConjectures.Bridge

end

/-! ## La solution (énoncé recopié tel quel de la plateforme) -/

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem solution (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ),
      zetaFunction p f *
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * n) = 1 - C ((Nat.card k : ℤ) ^ n) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        ∀ t : ℂ, t ≠ 0 →
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, aeval t (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
              aeval (((Nat.card k : ℂ) ^ n * t)⁻¹) (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * n + 1)).filter Odd,
                aeval (((Nat.card k : ℂ) ^ n * t)⁻¹) (P i)) /
              (∏ i ∈ (Finset.range (2 * n + 1)).filter Even,
                aeval (((Nat.card k : ℂ) ^ n * t)⁻¹) (P i)) =
            ε * (((Nat.card k : ℝ) ^ ((n : ℝ) *
                ((∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ) : ℤ) : ℝ)
                  / 2) : ℝ) : ℂ) *
              t ^ (∑ i ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) *
              ((∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, aeval t (P i)) /
                (∏ i ∈ (Finset.range (2 * n + 1)).filter Even, aeval t (P i)))) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * n - 1 →
        α (2 * n - i) = (α i).map fun a => (Nat.card k : ℂ) ^ n / a) :=
  WeilConjectures.Bridge.rationality_functional_equation_proof p k n X f hproj
