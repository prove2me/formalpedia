-- Prove2me | solution 1 for WeilConjectures.exists_deligne_weil_charpolys
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:01:35.371315+00:00
-- url     : https://prove2.me/submissions/ddb2c7e4-dec1-4111-8a47-4183058aaf90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_rationality
import Theorems.Thm_WeilConjectures_weil_conjectures_curves
import Theorems.Thm_WeilConjectures_projectiveSpace_zeta
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
import Theorems.Thm_WeilConjectures_zeta_coprime_reciprocity_of_ge_two
import Theorems.Thm_WeilConjectures_zeta_coprime_weight_purity_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

attribute [local instance] MvPolynomial.gradedAlgebra

section PolynomialReciprocity

private lemma coeff_comp_C_mul_X (P : ℚ[X]) (a : ℚ) (j : ℕ) :
    (P.comp (C a * X)).coeff j = P.coeff j * a ^ j := by
  induction P using Polynomial.induction_on' generalizing j with
  | add p q hp hq =>
    simp [Polynomial.add_comp, hp, hq, add_mul]
  | monomial n r =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial]
    by_cases h : n = j
    · subst h; simp
    · simp [h]

private lemma natDegree_comp_C_mul_X (P : ℚ[X]) {a : ℚ} (ha : a ≠ 0) :
    (P.comp (C a * X)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ ha, mul_one]

private lemma coeff_reverse_comp_C_mul_X (P : ℚ[X]) {a : ℚ} (ha : a ≠ 0) (m : ℕ) :
    ((P.comp (C a * X)).reverse).coeff m =
      if m ≤ P.natDegree then P.coeff (P.natDegree - m) * a ^ (P.natDegree - m) else 0 := by
  have hdeg_comp : (P.comp (C a * X)).natDegree = P.natDegree := natDegree_comp_C_mul_X P ha
  by_cases hm : m ≤ P.natDegree
  · rw [if_pos hm, Polynomial.coeff_reverse, ← hdeg_comp,
      Polynomial.revAt_le (hdeg_comp.symm ▸ hm), hdeg_comp, coeff_comp_C_mul_X]
  · rw [if_neg hm, Polynomial.coeff_reverse, hdeg_comp,
      Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hm), coeff_comp_C_mul_X,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hm), zero_mul]

private lemma reverse_one_poly {R : Type*} [Semiring R] : (1 : R[X]).reverse = 1 := by
  simpa using (Polynomial.reverse_C (1 : R))

private lemma reverse_natDegree_of_coeff_zero_ne_zero {R : Type*} [Semiring R] [NoZeroDivisors R]
    {P : R[X]} (hP0 : P.coeff 0 ≠ 0) :
    P.reverse.natDegree = P.natDegree := by
  have htrail : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP0)
  rw [Polynomial.reverse_natDegree, htrail, Nat.sub_zero]

private lemma reverse_reverse_of_coeff_zero_ne_zero {R : Type*} [Semiring R] [NoZeroDivisors R]
    {P : R[X]} (hP0 : P.coeff 0 ≠ 0) :
    P.reverse.reverse = P := by
  have hdeg : P.reverse.natDegree = P.natDegree := reverse_natDegree_of_coeff_zero_ne_zero hP0
  ext m
  rw [Polynomial.coeff_reverse, hdeg, Polynomial.coeff_reverse, Polynomial.revAt_invol]

private lemma monic_reverse_of_coeff_zero_eq_one {P : ℚ[X]} (hP0 : P.coeff 0 = 1) :
    P.reverse.Monic := by
  have hP0_ne : P.coeff 0 ≠ 0 := by rw [hP0]; exact one_ne_zero
  rw [Polynomial.Monic, Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP0_ne), hP0]

private lemma reverse_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (c : R) :
    (Polynomial.X - C c : R[X]).reverse = 1 - C c * Polynomial.X := by
  have hdeg : (Polynomial.X - C c : R[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C c
  ext m
  rcases m with _ | _ | m
  · simp [Polynomial.coeff_reverse, hdeg]
  · simp [Polynomial.coeff_reverse, hdeg, Polynomial.coeff_one]
  · rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_eq_self_of_lt (by omega : 1 < m + 2)]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one]

private lemma reverse_C_mul_X_sub_C {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {a : R} (ha : a ≠ 0) (b : R) :
    (C a * Polynomial.X - C b : R[X]).reverse = C a - C b * Polynomial.X := by
  have hdeg : (C a * Polynomial.X - C b : R[X]).natDegree = 1 := by
    have h1 : (C a * Polynomial.X : R[X]).natDegree = 1 := Polynomial.natDegree_C_mul_X a ha
    rw [sub_eq_add_neg, ← map_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact h1
    · rw [h1, Polynomial.natDegree_C]; omega
  ext m
  rcases m with _ | _ | m
  · simp [Polynomial.coeff_reverse, hdeg]
  · simp [Polynomial.coeff_reverse, hdeg]
  · rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_eq_self_of_lt (by omega : 1 < m + 2)]
    simp [Polynomial.coeff_sub]

private lemma reverse_one_sub_C_mul_X {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {a : R} (ha : a ≠ 0) :
    (1 - C a * Polynomial.X : R[X]).reverse = Polynomial.X - C a := by
  have hdeg : (1 - C a * Polynomial.X : R[X]).natDegree = 1 := by
    have h1 : (C (-a) * Polynomial.X : R[X]).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X (-a) (neg_ne_zero.mpr ha)
    have heq : (1 - C a * Polynomial.X : R[X]) = C (-a) * Polynomial.X + C 1 := by
      rw [map_neg, map_one]; ring
    rw [heq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact h1
    · rw [h1, Polynomial.natDegree_C]; omega
  ext m
  rcases m with _ | _ | m
  · simp [Polynomial.coeff_reverse, hdeg, Polynomial.coeff_one]
  · simp [Polynomial.coeff_reverse, hdeg]
  · rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_eq_self_of_lt (by omega : 1 < m + 2)]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one]

private lemma reverse_multiset_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (s : Multiset R[X]) :
    s.prod.reverse = (s.map Polynomial.reverse).prod := by
  induction s using Multiset.induction with
  | empty => simp [reverse_one_poly]
  | cons a s ih =>
    rw [Multiset.prod_cons, Polynomial.reverse_mul_of_domain, Multiset.map_cons,
      Multiset.prod_cons, ih]

private lemma reverse_finset_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] {ι : Type*}
    (s : Finset ι) (f : ι → R[X]) :
    (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  classical
  induction s using Finset.induction with
  | empty => simp [reverse_one_poly]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Polynomial.reverse_mul_of_domain, Finset.prod_insert ha, ih]

private lemma reverse_map_of_injective {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (hφ : Function.Injective φ) (P : R[X]) :
    (P.map φ).reverse = P.reverse.map φ := by
  have hdeg : (P.map φ).natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective hφ P
  ext m
  rw [Polynomial.coeff_reverse, hdeg, Polynomial.coeff_map, Polynomial.coeff_map,
    Polynomial.coeff_reverse]

private noncomputable def poincareDual (a : ℚ) (P : ℚ[X]) : ℚ[X] :=
  C (P.coeff 0)⁻¹ * (P.comp (C a * X)).reverse

private lemma poincareDual_natDegree {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} (hP0 : P.coeff 0 ≠ 0) :
    (poincareDual a P).natDegree = P.natDegree := by
  unfold poincareDual
  have hcomp0 : (P.comp (C a * X)).coeff 0 ≠ 0 := by
    rw [coeff_comp_C_mul_X, pow_zero, mul_one]; exact hP0
  have hrev_deg : ((P.comp (C a * X)).reverse).natDegree = P.natDegree := by
    rw [reverse_natDegree_of_coeff_zero_ne_zero hcomp0, natDegree_comp_C_mul_X P ha]
  rw [Polynomial.natDegree_C_mul (inv_ne_zero hP0), hrev_deg]

private lemma poincareDual_monic {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} (hP0 : P.coeff 0 ≠ 0) :
    (poincareDual a P).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, poincareDual_natDegree ha hP0]
  unfold poincareDual
  rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X P ha, if_pos le_rfl,
    Nat.sub_self, pow_zero, mul_one, inv_mul_cancel₀ hP0]

private lemma poincareDual_coeff_zero {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]} (hP : P.Monic) :
    (poincareDual a P).coeff 0 = (P.coeff 0)⁻¹ * a ^ P.natDegree := by
  unfold poincareDual
  rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X P ha, if_pos (Nat.zero_le _),
    Nat.sub_zero, hP.coeff_natDegree, one_mul]

private lemma poincareDual_coeff_zero_ne_zero {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]}
    (hP : P.Monic) (hP0 : P.coeff 0 ≠ 0) :
    (poincareDual a P).coeff 0 ≠ 0 := by
  rw [poincareDual_coeff_zero ha hP]
  exact mul_ne_zero (inv_ne_zero hP0) (pow_ne_zero _ ha)

private lemma poincareDual_mul {a : ℚ} (P Q : ℚ[X]) :
    poincareDual a (P * Q) = poincareDual a P * poincareDual a Q := by
  unfold poincareDual
  rw [Polynomial.mul_coeff_zero, mul_inv_rev, mul_comm (Q.coeff 0)⁻¹,
    Polynomial.mul_comp, Polynomial.reverse_mul_of_domain, map_mul]
  ring

private lemma poincareDual_one (a : ℚ) : poincareDual a 1 = 1 := by
  unfold poincareDual
  simp [reverse_one_poly]

private lemma poincareDual_multiset_prod {a : ℚ} (s : Multiset ℚ[X]) :
    poincareDual a s.prod = (s.map (poincareDual a)).prod := by
  induction s using Multiset.induction with
  | empty => simp [poincareDual_one]
  | cons p s ih =>
    rw [Multiset.prod_cons, poincareDual_mul, Multiset.map_cons, Multiset.prod_cons, ih]

private lemma poincareDual_invol {a : ℚ} (ha : a ≠ 0) {P : ℚ[X]}
    (hP : P.Monic) (hP0 : P.coeff 0 ≠ 0) :
    poincareDual a (poincareDual a P) = P := by
  have hDdeg : (poincareDual a P).natDegree = P.natDegree := poincareDual_natDegree ha hP0
  have hD0 : (poincareDual a P).coeff 0 = (P.coeff 0)⁻¹ * a ^ P.natDegree :=
    poincareDual_coeff_zero ha hP
  ext m
  conv_lhs => rw [poincareDual]
  rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X (poincareDual a P) ha, hDdeg]
  by_cases hm : m ≤ P.natDegree
  · rw [if_pos hm, hD0]
    conv_lhs => rw [poincareDual]
    rw [Polynomial.coeff_C_mul, coeff_reverse_comp_C_mul_X P ha,
      if_pos (Nat.sub_le _ _), Nat.sub_sub_self hm]
    have hpow : a ^ m * a ^ (P.natDegree - m) = a ^ P.natDegree := by
      rw [← pow_add, Nat.add_sub_of_le hm]
    have ha_pow : a ^ P.natDegree ≠ 0 := pow_ne_zero _ ha
    calc
      ((P.coeff 0)⁻¹ * a ^ P.natDegree)⁻¹ * ((P.coeff 0)⁻¹ * (P.coeff m * a ^ m) * a ^ (P.natDegree - m))
          = (P.coeff 0 * (a ^ P.natDegree)⁻¹) * ((P.coeff 0)⁻¹ * (P.coeff m * (a ^ m * a ^ (P.natDegree - m)))) := by
            rw [mul_inv, inv_inv]; ring
      _ = P.coeff m * (P.coeff 0 * (P.coeff 0)⁻¹) * (a ^ P.natDegree * (a ^ P.natDegree)⁻¹) := by
            rw [hpow]; ring
      _ = P.coeff m := by
            rw [mul_inv_cancel₀ hP0, mul_inv_cancel₀ ha_pow, mul_one, mul_one]
  · rw [if_neg hm, mul_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hm)]

private lemma poincareDual_irreducible {a : ℚ} (ha : a ≠ 0) {r : ℚ[X]}
    (hr_monic : r.Monic) (hr0 : r.coeff 0 ≠ 0) (hr_irr : Irreducible r) :
    Irreducible (poincareDual a r) := by
  have hr_deg_pos : 0 < r.natDegree := hr_irr.natDegree_pos
  have hD_deg_pos : 0 < (poincareDual a r).natDegree := by
    rw [poincareDual_natDegree ha hr0]; exact hr_deg_pos
  have hD_not_unit : ¬ IsUnit (poincareDual a r) := by
    intro hu
    have h0 : (poincareDual a r).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  refine ⟨hD_not_unit, ?_⟩
  intro u v huv
  have hu_ne : u ≠ 0 := by
    intro h0; subst h0; simp at huv
    exact (poincareDual_monic ha hr0).ne_zero huv
  have hv_ne : v ≠ 0 := by
    intro h0; subst h0; simp at huv
    exact (poincareDual_monic ha hr0).ne_zero huv
  let u' : ℚ[X] := C u.leadingCoeff⁻¹ * u
  let v' : ℚ[X] := C v.leadingCoeff⁻¹ * v
  have hu'_monic : u'.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hu_ne)]
  have hv'_monic : v'.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hv_ne)]
  have hlc : u.leadingCoeff * v.leadingCoeff = 1 := by
    have := congrArg Polynomial.leadingCoeff huv
    rw [(poincareDual_monic ha hr0).leadingCoeff, Polynomial.leadingCoeff_mul] at this
    exact this.symm
  have huv' : poincareDual a r = u' * v' := by
    have hinv : u.leadingCoeff⁻¹ * v.leadingCoeff⁻¹ = 1 := by
      rw [← mul_inv, hlc, inv_one]
    calc
      poincareDual a r = u * v := huv
      _ = C (u.leadingCoeff⁻¹ * v.leadingCoeff⁻¹) * (u * v) := by rw [hinv, map_one, one_mul]
      _ = (C u.leadingCoeff⁻¹ * u) * (C v.leadingCoeff⁻¹ * v) := by rw [map_mul]; ring
  have hD0 : (poincareDual a r).coeff 0 ≠ 0 := poincareDual_coeff_zero_ne_zero ha hr_monic hr0
  have hu'0 : u'.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (fun p : ℚ[X] => p.coeff 0) huv'
    rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
    exact hD0 this
  have hv'0 : v'.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (fun p : ℚ[X] => p.coeff 0) huv'
    rw [Polynomial.mul_coeff_zero, h0, mul_zero] at this
    exact hD0 this
  have hr_fac : r = poincareDual a u' * poincareDual a v' := by
    rw [← poincareDual_mul, ← huv', poincareDual_invol ha hr_monic hr0]
  rcases hr_irr.isUnit_or_isUnit hr_fac with hdu | hdv
  · left
    have hdeg0 : u'.natDegree = 0 := by
      rw [← poincareDual_natDegree ha hu'0]
      exact Polynomial.natDegree_eq_zero_of_isUnit hdu
    have hu_deg0 : u.natDegree = 0 := by
      have : u'.natDegree = u.natDegree :=
        Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hu_ne))
      omega
    exact Polynomial.isUnit_iff_degree_eq_zero.mpr
      ((Polynomial.degree_eq_natDegree hu_ne).trans (by exact_mod_cast hu_deg0))
  · right
    have hdeg0 : v'.natDegree = 0 := by
      rw [← poincareDual_natDegree ha hv'0]
      exact Polynomial.natDegree_eq_zero_of_isUnit hdv
    have hv_deg0 : v.natDegree = 0 := by
      have : v'.natDegree = v.natDegree :=
        Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hv_ne))
      omega
    exact Polynomial.isUnit_iff_degree_eq_zero.mpr
      ((Polynomial.degree_eq_natDegree hv_ne).trans (by exact_mod_cast hv_deg0))

private lemma monic_of_mem_normalizedFactors {P r : ℚ[X]}
    (hr : r ∈ UniqueFactorizationMonoid.normalizedFactors P) : r.Monic := by
  have hirr : Irreducible r := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
  have hnorm : normalize r = r := UniqueFactorizationMonoid.normalize_normalized_factor r hr
  exact (Polynomial.normalize_eq_self_iff_monic hirr.ne_zero).mp hnorm

private lemma aeval_poincareDual_eq_zero_iff {a : ℚ} (ha : a ≠ 0) {r : ℚ[X]}
    (hr_monic : r.Monic) (hr0 : r.coeff 0 ≠ 0) (z : ℂ) :
    aeval z (poincareDual a r) = 0 ↔ z ≠ 0 ∧ aeval ((a : ℂ) / z) r = 0 := by
  have hD0 : (poincareDual a r).coeff 0 ≠ 0 := poincareDual_coeff_zero_ne_zero ha hr_monic hr0
  constructor
  · intro hz
    have hz_ne : z ≠ 0 := by
      intro h0; subst h0
      have : aeval (0 : ℂ) (poincareDual a r) = ((poincareDual a r).coeff 0 : ℂ) := by
        simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
      rw [this] at hz
      exact hD0 (Rat.cast_injective (α := ℂ) (by simpa using hz))
    refine ⟨hz_ne, ?_⟩
    unfold poincareDual at hz
    rw [map_mul, aeval_C, mul_eq_zero] at hz
    have hinv_ne : (((r.coeff 0)⁻¹ : ℚ) : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero hr0
    have hrev0 : aeval z ((r.comp (C a * X)).reverse) = 0 := hz.resolve_left hinv_ne
    have : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz_ne)
    have hinv_z : ⅟(z⁻¹) = z := by rw [invOf_eq_inv, inv_inv]
    have hrev0' : Polynomial.eval₂ (algebraMap ℚ ℂ) (⅟(z⁻¹)) (r.comp (C a * X)).reverse = 0 := by
      rw [hinv_z]; exact hrev0
    have hcomp0 : Polynomial.eval₂ (algebraMap ℚ ℂ) z⁻¹ (r.comp (C a * X)) = 0 :=
      (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℚ ℂ) z⁻¹ (r.comp (C a * X))).mp hrev0'
    have hcomp_eval :
        Polynomial.eval₂ (algebraMap ℚ ℂ) z⁻¹ (r.comp (C a * X)) =
          aeval ((a : ℂ) / z) r := by
      rw [← Polynomial.aeval_def, Polynomial.aeval_comp, map_mul, aeval_C, aeval_X, div_eq_mul_inv]
      rfl
    rwa [hcomp_eval] at hcomp0
  · rintro ⟨hz_ne, hroot⟩
    have : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz_ne)
    have hinv_z : ⅟(z⁻¹) = z := by rw [invOf_eq_inv, inv_inv]
    unfold poincareDual
    rw [map_mul, aeval_C]
    suffices hrev0 : aeval z ((r.comp (C a * X)).reverse) = 0 by rw [hrev0, mul_zero]
    change Polynomial.eval₂ (algebraMap ℚ ℂ) z (r.comp (C a * X)).reverse = 0
    rw [← hinv_z, Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℚ ℂ) z⁻¹ (r.comp (C a * X))]
    rw [← Polynomial.aeval_def, Polynomial.aeval_comp, map_mul, aeval_C, aeval_X]
    simpa [div_eq_mul_inv] using hroot

end PolynomialReciprocity

section DimZero

private lemma isProper_of_isProjectiveOver (k : Type) [Field k] {X : Scheme.{0}}
    {f : X ⟶ Spec (.of k)} (hproj : IsProjectiveOver k f) : IsProper f := by
  classical
  obtain ⟨N, i, hi, rfl⟩ := hproj
  unfold projectiveSpace.toSpec
  have : IsClosedImmersion i := hi
  let A0 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0
  have hft : Algebra.FiniteType A0 (MvPolynomial (Fin (N + 1)) k) := by
    refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
    rw [eq_top_iff]
    intro p _
    clear ‹p ∈ ⊤›
    induction p using MvPolynomial.induction_on with
    | C c =>
      have hc : MvPolynomial.C c ∈ A0 := MvPolynomial.isHomogeneous_C (Fin (N + 1)) c
      change MvPolynomial.C c ∈ Algebra.adjoin A0 _
      have : (algebraMap A0 (MvPolynomial (Fin (N + 1)) k)) ⟨MvPolynomial.C c, hc⟩ =
          MvPolynomial.C c := rfl
      rw [← this]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p j hp =>
      exact Subalgebra.mul_mem _ hp
        (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) :=
    inferInstance
  have hbij : Function.Bijective (algebraMap k A0) := by
    constructor
    · intro x y hxy
      have hval : (MvPolynomial.C x : MvPolynomial (Fin (N + 1)) k) = MvPolynomial.C y :=
        congrArg Subtype.val hxy
      exact MvPolynomial.C_injective _ _ hval
    · rintro ⟨p, hp⟩
      refine ⟨MvPolynomial.constantCoeff p, Subtype.ext ?_⟩
      change MvPolynomial.C (MvPolynomial.constantCoeff p) = p
      ext d
      by_cases hd : d = 0
      · subst hd
        simp [MvPolynomial.coeff_C, MvPolynomial.constantCoeff_eq]
      · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hd)]
        have hcoeff0 : MvPolynomial.coeff d p = 0 := by
          by_contra hne0
          have h0 := hp hne0
          simp [Finsupp.weight_apply, Finsupp.sum_fintype] at h0
          exact hd (Finsupp.ext h0)
        exact hcoeff0.symm
  have : IsIso (CommRingCat.ofHom (algebraMap k A0)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k A0))) := inferInstance
  have : IsProper (Spec.map (CommRingCat.ofHom (algebraMap k A0))) := inferInstance
  infer_instance

private lemma solve_dim_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 0 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ C : ℕ → ℚ[X],
      (∀ i ≤ 2 * 0, (C i).Monic ∧ (C i).coeff 0 ≠ 0) ∧
      (C 0 = Polynomial.X - 1) ∧
      (zetaFunction p f *
          ∏ i ∈ (Finset.range (2 * 0 + 1)).filter Even, (((C i).reverse : ℚ[X]) : PowerSeries ℚ) =
        ∏ i ∈ (Finset.range (2 * 0 + 1)).filter Odd, (((C i).reverse : ℚ[X]) : PowerSeries ℚ)) ∧
      (∀ i ≤ 2 * 0,
        (C (2 * 0 - i)).natDegree = (C i).natDegree ∧
        (C i).coeff 0 • C (2 * 0 - i) =
          ((C i).comp (Polynomial.C ((Nat.card k : ℚ) ^ 0) * Polynomial.X)).reverse) ∧
      (∀ i ≤ 2 * 0, ∀ z : ℂ, aeval z (C i) = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  have : IsProper f := isProper_of_isProjectiveOver k hproj
  have : Smooth f := SmoothOfRelativeDimension.smooth 0 f
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  have : LocallyQuasiFinite f := ⟨fun {U} hU {V} hV e => by
    have het := f.etale_appLE hU hV e
    let _ := (f.appLE U V e).hom.toAlgebra
    have : Algebra.Etale _ _ := het
    exact inferInstanceAs (Algebra.QuasiFinite _ _)⟩
  have : IsFinite f := (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsAffineHom f := inferInstance
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Subsingleton ↥(Spec (.of k)) :=
    ⟨fun x y => PrimeSpectrum.ext (by
      have := x.isPrime
      have := y.isPrime
      rw [Ideal.eq_bot_of_prime x.asIdeal, Ideal.eq_bot_of_prime y.asIdeal])⟩
  have : IrreducibleSpace ↥X :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := f)
  have : Nonempty ↥X := inferInstance
  have hbij : Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom :=
    (AlgebraicGeometry.geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth f).mp
      inferInstance
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso f.appTop := by
    have : f.appTop = (Scheme.ΓSpecIso (.of k)).hom ≫ ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
      simp
    rw [this]
    infer_instance
  have : IsIso f := by
    have hf : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ (Spec (.of k)).isoSpec.inv := by
      rw [Scheme.isoSpec_hom_naturality_assoc]
      simp
    rw [hf]
    infer_instance
  have hpc : ∀ m : ℕ, 1 ≤ m → pointCount p f m = 1 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    simp only [pointCount, dif_neg hm0, pointsOver]
    have : NeZero m := ⟨hm0⟩
    let L := FiniteField.Extension k p m
    let g : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
    have hequiv : {x : Spec (.of L) ⟶ X // x ≫ f = g} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨g ≫ inv f, by simp⟩
        left_inv := fun ⟨x, hx⟩ => Subtype.ext (by
          change g ≫ inv f = x
          rw [← hx, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
        right_inv := fun () => rfl }
    rw [Nat.card_congr hequiv, Nat.card_unique]
  have hP0 := WeilConjectures.projectiveSpace_zeta p k 0
  have hpc_eq : pointCount p f = pointCount p (projectiveSpace.toSpec k 0) := by
    funext m
    by_cases hm : m = 0
    · subst hm; simp [pointCount]
    · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm
      rw [hpc m hm1, hP0.1 m hm1]
      simp
  have hzeta0 : zetaFunction p f * (1 - PowerSeries.X) = 1 := by
    have hz : zetaFunction p f = zetaFunction p (projectiveSpace.toSpec k 0) := by
      simp [zetaFunction, hpc_eq]
    rw [hz]
    simpa using hP0.2
  refine ⟨fun _ => Polynomial.X - 1, ?_, rfl, ?_, ?_, ?_⟩
  · intro i _
    exact ⟨Polynomial.monic_X_sub_C 1, by simp⟩
  · have hrev : ((Polynomial.X - 1 : ℚ[X]).reverse : ℚ[X]) = 1 - Polynomial.X := by
      simpa using reverse_X_sub_C (1 : ℚ)
    have hev : (Finset.range (2 * 0 + 1)).filter Even = {0} := by decide
    have hodd : (Finset.range (2 * 0 + 1)).filter Odd = ∅ := by decide
    rw [hev, hodd, Finset.prod_singleton, Finset.prod_empty, hrev]
    simpa using hzeta0
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    refine ⟨rfl, ?_⟩
    have hcomp : ((Polynomial.X - 1 : ℚ[X]).comp (C ((Nat.card k : ℚ) ^ 0) * Polynomial.X)) =
        Polynomial.X - 1 := by simp
    rw [hcomp]
    have hrev : (Polynomial.X - 1 : ℚ[X]).reverse = 1 - Polynomial.X := by
      simpa using reverse_X_sub_C (1 : ℚ)
    rw [hrev]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_sub,
      neg_smul, one_smul]
    ring
  · intro i hi z hz
    have hi0 : i = 0 := by omega
    subst hi0
    have hz1 : z = 1 := sub_eq_zero.mp (by simpa using hz)
    subst hz1
    simp

end DimZero

section DimOne

private lemma solve_dim_one (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ C : ℕ → ℚ[X],
      (∀ i ≤ 2 * 1, (C i).Monic ∧ (C i).coeff 0 ≠ 0) ∧
      (C 0 = Polynomial.X - 1) ∧
      (zetaFunction p f *
          ∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, (((C i).reverse : ℚ[X]) : PowerSeries ℚ) =
        ∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd, (((C i).reverse : ℚ[X]) : PowerSeries ℚ)) ∧
      (∀ i ≤ 2 * 1,
        (C (2 * 1 - i)).natDegree = (C i).natDegree ∧
        (C i).coeff 0 • C (2 * 1 - i) =
          ((C i).comp (Polynomial.C ((Nat.card k : ℚ) ^ 1) * Polynomial.X)).reverse) ∧
      (∀ i ≤ 2 * 1, ∀ z : ℂ, aeval z (C i) = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  obtain ⟨P, α, hzeta, hP0, hP2, hP1_all, _, hPD_all, hwt_all⟩ :=
    WeilConjectures.weil_conjectures_curves p k X f hproj
  have ⟨hP1_map, hα1_ne⟩ := hP1_all 1 le_rfl le_rfl
  have hPD1 : α 1 = (α 1).map fun a => (Nat.card k : ℂ) ^ 1 / a := hPD_all 1 le_rfl le_rfl
  have hwt1 : ∀ a ∈ α 1, ‖a‖ = (Nat.card k : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa using hwt_all 1 le_rfl le_rfl
  let Q1 : ℚ[X] := (P 1).map (Int.castRingHom ℚ)
  have hQ1_map : Q1.map (algebraMap ℚ ℂ) = ((α 1).map fun a => 1 - C a * Polynomial.X).prod := by
    have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
      ext; simp
    rw [Polynomial.map_map, hcomp, hP1_map]
  have hQ1_c0 : Q1.coeff 0 = 1 := by
    apply Rat.cast_injective (α := ℂ)
    have h0 : (Q1.map (algebraMap ℚ ℂ)).coeff 0 = 1 := by
      rw [hQ1_map]
      induction (α 1) using Multiset.induction with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero]
        simp [ih]
    simpa [Polynomial.coeff_map] using h0
  have hQ1_ne : Q1 ≠ 0 := by
    intro h0; rw [h0, Polynomial.coeff_zero] at hQ1_c0; exact zero_ne_one hQ1_c0
  let C1 : ℚ[X] := Q1.reverse
  have hC1_monic : C1.Monic := monic_reverse_of_coeff_zero_eq_one hQ1_c0
  have hC1_c0_ne : C1.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ1_ne
  have hC1_rev : C1.reverse = Q1 :=
    reverse_reverse_of_coeff_zero_ne_zero (by rw [hQ1_c0]; exact one_ne_zero)
  have hC1_map : C1.map (algebraMap ℚ ℂ) = ((α 1).map fun a => Polynomial.X - C a).prod := by
    have hinj : Function.Injective (algebraMap ℚ ℂ) := Rat.cast_injective
    rw [← reverse_map_of_injective (algebraMap ℚ ℂ) hinj Q1, hQ1_map, reverse_multiset_prod,
      Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a ha => ?_
    exact reverse_one_sub_C_mul_X (hα1_ne a ha)
  let q : ℚ := (Nat.card k : ℚ)
  have hq_ne : q ≠ 0 := by
    have : 0 < Nat.card k := Nat.card_pos
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt this)
  let Cfun : ℕ → ℚ[X] := fun i =>
    match i with
    | 0 => Polynomial.X - 1
    | 1 => C1
    | 2 => Polynomial.X - C q
    | _ => 1
  have hrev0 : ((Polynomial.X - 1 : ℚ[X]).reverse : ℚ[X]) = (P 0).map (Int.castRingHom ℚ) := by
    rw [hP0, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
    simpa using reverse_X_sub_C (1 : ℚ)
  have hrev2 : ((Polynomial.X - C q : ℚ[X]).reverse : ℚ[X]) = (P 2).map (Int.castRingHom ℚ) := by
    rw [show P 2 = 1 - C ((Nat.card k : ℤ) ^ 1) * Polynomial.X from hP2, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    simpa [q] using reverse_X_sub_C q
  have hdegX1 : (Polynomial.X - 1 : ℚ[X]).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C (1 : ℚ)
  refine ⟨Cfun, ?_, rfl, ?_, ?_, ?_⟩
  · intro i hi
    rcases i with _ | _ | _ | i
    · exact ⟨by simpa [Cfun] using Polynomial.monic_X_sub_C (1 : ℚ), by simp [Cfun]⟩
    · exact ⟨hC1_monic, hC1_c0_ne⟩
    · exact ⟨Polynomial.monic_X_sub_C q, by simp [Cfun, hq_ne]⟩
    · omega
  · have hev : (Finset.range (2 * 1 + 1)).filter Even = {0, 2} := by decide
    have hodd : (Finset.range (2 * 1 + 1)).filter Odd = {1} := by decide
    rw [hev, hodd] at hzeta ⊢
    simp only [Finset.prod_pair (by decide : (0 : ℕ) ≠ 2), Finset.prod_singleton, Cfun] at hzeta ⊢
    rw [hrev0, hrev2, hC1_rev]
    exact hzeta
  · intro i hi
    rcases i with _ | _ | _ | i
    · refine ⟨by simp [Cfun, hdegX1], ?_⟩
      change (Polynomial.X - 1 : ℚ[X]).coeff 0 • (Polynomial.X - C q) =
        ((Polynomial.X - 1 : ℚ[X]).comp (C (q ^ 1) * Polynomial.X)).reverse
      have hcomp : ((Polynomial.X - 1 : ℚ[X]).comp (C (q ^ 1) * Polynomial.X)) =
          C q * Polynomial.X - C 1 := by simp [Polynomial.sub_comp]
      rw [hcomp, reverse_C_mul_X_sub_C hq_ne 1]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero, zero_sub,
        neg_smul, one_smul, map_one, one_mul]
      ring
    · refine ⟨rfl, ?_⟩
      change C1.coeff 0 • C1 = (C1.comp (C (q ^ 1) * Polynomial.X)).reverse
      rw [pow_one]
      have hinj : Function.Injective (Polynomial.map (algebraMap ℚ ℂ)) :=
        Polynomial.map_injective _ Rat.cast_injective
      apply hinj
      rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C]
      conv_rhs =>
        rw [← reverse_map_of_injective (algebraMap ℚ ℂ) Rat.cast_injective,
          Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
      rw [hC1_map]
      have hC1_c0_C : (algebraMap ℚ ℂ) (C1.coeff 0) = ((α 1).map fun a => -a).prod := by
        have h := congrArg (fun p : ℂ[X] => p.coeff 0) hC1_map
        rw [Polynomial.coeff_map] at h
        rw [h]
        induction (α 1) using Multiset.induction with
        | empty => simp
        | cons a s ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ih]
          simp
      rw [hC1_c0_C]
      have hcomp_prod :
          (((α 1).map fun a => Polynomial.X - C a).prod).comp (C ((algebraMap ℚ ℂ) q) * Polynomial.X) =
            ((α 1).map fun a => C (q : ℂ) * Polynomial.X - C a).prod := by
        rw [Polynomial.multiset_prod_comp, Multiset.map_map]
        congr 1
        refine Multiset.map_congr rfl fun a _ => ?_
        simp [Polynomial.sub_comp]
      rw [hcomp_prod, reverse_multiset_prod, Multiset.map_map]
      have hqC_ne : (q : ℂ) ≠ 0 := by exact_mod_cast hq_ne
      have hstep :
          ((α 1).map (Polynomial.reverse ∘ fun a => C (q : ℂ) * Polynomial.X - C a)).prod =
            ((α 1).map fun a => C (-a) * (Polynomial.X - C ((q : ℂ) / a))).prod := by
        congr 1
        refine Multiset.map_congr rfl fun a ha => ?_
        have ha0 : a ≠ 0 := hα1_ne a ha
        change (C (q : ℂ) * Polynomial.X - C a).reverse =
          C (-a) * (Polynomial.X - C ((q : ℂ) / a))
        rw [reverse_C_mul_X_sub_C hqC_ne a, mul_sub, ← map_mul, neg_mul,
          mul_div_cancel₀ _ ha0, map_neg, map_neg]
        ring
      rw [hstep]
      have hsplit :
          ((α 1).map fun a => C (-a) * (Polynomial.X - C ((q : ℂ) / a))).prod =
            C (((α 1).map fun a => -a).prod) *
              ((α 1).map fun a => Polynomial.X - C ((q : ℂ) / a)).prod := by
        induction (α 1) using Multiset.induction with
        | empty => simp
        | cons a s ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.map_cons, Multiset.prod_cons,
            Multiset.map_cons, Multiset.prod_cons, map_mul]
          ring
      rw [hsplit]
      congr 1
      have hPD1' : (α 1).map (fun a => Polynomial.X - C ((q : ℂ) / a)) =
          ((α 1).map fun a => (q : ℂ) / a).map (fun b => Polynomial.X - C b) := by
        rw [Multiset.map_map]; rfl
      rw [hPD1']
      have hPD1_q : (α 1).map (fun a => (q : ℂ) / a) = α 1 := by
        simpa [q] using hPD1.symm
      rw [hPD1_q]
    · refine ⟨by simp [Cfun, hdegX1], ?_⟩
      change (Polynomial.X - C q : ℚ[X]).coeff 0 • (Polynomial.X - 1) =
        ((Polynomial.X - C q : ℚ[X]).comp (C (q ^ 1) * Polynomial.X)).reverse
      have hcomp : ((Polynomial.X - C q : ℚ[X]).comp (C (q ^ 1) * Polynomial.X)) =
          C q * Polynomial.X - C q := by simp [Polynomial.sub_comp]
      rw [hcomp, reverse_C_mul_X_sub_C hq_ne q]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
        Polynomial.smul_eq_C_mul, map_neg]
      ring
    · omega
  · intro i hi z hz
    rcases i with _ | _ | _ | i
    · have hz1 : z = 1 := sub_eq_zero.mp (by simpa [Cfun] using hz)
      subst hz1; simp
    · have hroot : Polynomial.IsRoot (C1.map (algebraMap ℚ ℂ)) z := by
        rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
      rw [hC1_map, Polynomial.IsRoot, Polynomial.eval_multiset_prod,
        Multiset.prod_eq_zero_iff, Multiset.mem_map] at hroot
      obtain ⟨p0, hp0, hz0⟩ := hroot
      rw [Multiset.mem_map] at hp0
      obtain ⟨a, ha, rfl⟩ := hp0
      have hza : z = a := sub_eq_zero.mp (by simpa using hz0)
      subst hza
      simpa using le_of_eq (hwt1 z ha)
    · have hzq : z = (q : ℂ) := sub_eq_zero.mp (by simpa [Cfun] using hz)
      subst hzq
      simp [q]
    · omega

end DimOne

section DimGeTwo

private lemma exists_coprime_normalized_zeta (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ N D : ℚ[X], IsCoprime N D ∧ N.coeff 0 = 1 ∧ D.coeff 0 = 1 ∧
      zetaFunction p f * (D : PowerSeries ℚ) = (N : PowerSeries ℚ) := by
  obtain ⟨P, Q, hQ_ne, hPQ⟩ := WeilConjectures.rationality p k n X f hproj
  let g : ℚ[X] := EuclideanDomain.gcd P Q
  have hg_ne : g ≠ 0 := by
    intro h0
    have hQ0 : g ∣ Q := EuclideanDomain.gcd_dvd_right P Q
    rw [h0, zero_dvd_iff] at hQ0
    exact hQ_ne hQ0
  let P1 : ℚ[X] := P / g
  let Q1 : ℚ[X] := Q / g
  have hP1 : P = g * P1 := (EuclideanDomain.mul_div_cancel' hg_ne (EuclideanDomain.gcd_dvd_left P Q)).symm
  have hQ1 : Q = g * Q1 := (EuclideanDomain.mul_div_cancel' hg_ne (EuclideanDomain.gcd_dvd_right P Q)).symm
  have hQ1_ne : Q1 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hQ1; exact hQ_ne hQ1
  have hcop1 : IsCoprime P1 Q1 := by
    have hbez := EuclideanDomain.gcd_eq_gcd_ab P Q
    refine ⟨EuclideanDomain.gcdA P Q, EuclideanDomain.gcdB P Q, ?_⟩
    have hmul : g * (EuclideanDomain.gcdA P Q * P1 + EuclideanDomain.gcdB P Q * Q1) = g * 1 := by
      calc
        g * (EuclideanDomain.gcdA P Q * P1 + EuclideanDomain.gcdB P Q * Q1)
            = (g * P1) * EuclideanDomain.gcdA P Q + (g * Q1) * EuclideanDomain.gcdB P Q := by ring
        _ = P * EuclideanDomain.gcdA P Q + Q * EuclideanDomain.gcdB P Q := by rw [← hP1, ← hQ1]
        _ = g := hbez.symm
        _ = g * 1 := (mul_one g).symm
    exact mul_left_cancel₀ hg_ne hmul
  have hZ1 : zetaFunction p f * (Q1 : PowerSeries ℚ) = (P1 : PowerSeries ℚ) := by
    have hmul : (g : PowerSeries ℚ) * (zetaFunction p f * (Q1 : PowerSeries ℚ)) =
        (g : PowerSeries ℚ) * (P1 : PowerSeries ℚ) := by
      calc
        (g : PowerSeries ℚ) * (zetaFunction p f * (Q1 : PowerSeries ℚ))
            = zetaFunction p f * ((g * Q1 : ℚ[X]) : PowerSeries ℚ) := by
              rw [Polynomial.coe_mul]; ring
        _ = zetaFunction p f * (Q : PowerSeries ℚ) := by rw [← hQ1]
        _ = (P : PowerSeries ℚ) := hPQ
        _ = ((g * P1 : ℚ[X]) : PowerSeries ℚ) := by rw [hP1]
        _ = (g : PowerSeries ℚ) * (P1 : PowerSeries ℚ) := by rw [Polynomial.coe_mul]
    have hg_ps : (g : PowerSeries ℚ) ≠ 0 := by
      intro h0
      exact hg_ne (Polynomial.coe_injective (R := ℚ) (by simpa using h0))
    exact mul_left_cancel₀ hg_ps hmul
  have hZ0 : PowerSeries.constantCoeff (zetaFunction p f) = 1 := by
    unfold zetaFunction zetaOfCounts
    let L : PowerSeries ℚ :=
      PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (pointCount p f m : ℚ) / (m : ℚ)
    have hL0 : PowerSeries.constantCoeff L = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      simp [L]
    have hLsubst : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
    change MvPowerSeries.constantCoeff (PowerSeries.subst L (PowerSeries.exp ℚ)) = 1
    rw [PowerSeries.constantCoeff_subst hLsubst (PowerSeries.exp ℚ), finsum_eq_single _ 0]
    · simp [PowerSeries.coeff_exp]
    · intro k hk
      rw [map_pow, show MvPowerSeries.constantCoeff L = 0 from hL0, zero_pow hk, smul_zero]
  have hQ1_c0_eq : Q1.coeff 0 = P1.coeff 0 := by
    have h0 := congrArg PowerSeries.constantCoeff hZ1
    rw [map_mul, hZ0, one_mul] at h0
    simpa [Polynomial.constantCoeff_coe] using h0
  have hQ1_c0_ne : Q1.coeff 0 ≠ 0 := by
    intro hQ0
    have hP0 : P1.coeff 0 = 0 := hQ1_c0_eq.symm.trans hQ0
    have hX_Q : Polynomial.X ∣ Q1 := Polynomial.X_dvd_iff.mpr hQ0
    have hX_P : Polynomial.X ∣ P1 := Polynomial.X_dvd_iff.mpr hP0
    have hXu : IsUnit (Polynomial.X : ℚ[X]) := hcop1.isUnit_of_dvd' hX_P hX_Q
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hXu
    simp at hdeg0
  let c : ℚ := Q1.coeff 0
  let N : ℚ[X] := C c⁻¹ * P1
  let D : ℚ[X] := C c⁻¹ * Q1
  refine ⟨N, D, ?_, ?_, ?_, ?_⟩
  · rcases hcop1 with ⟨a, b, hab⟩
    refine ⟨C c * a, C c * b, ?_⟩
    calc
      (C c * a) * (C c⁻¹ * P1) + (C c * b) * (C c⁻¹ * Q1)
          = (C c * C c⁻¹) * (a * P1 + b * Q1) := by ring
      _ = 1 := by rw [← map_mul, mul_inv_cancel₀ hQ1_c0_ne, map_one, hab, mul_one]
  · simp [N, ← hQ1_c0_eq, c, inv_mul_cancel₀ hQ1_c0_ne]
  · simp [D, c, inv_mul_cancel₀ hQ1_c0_ne]
  · calc
      zetaFunction p f * (D : PowerSeries ℚ)
          = (C c⁻¹ : PowerSeries ℚ) * (zetaFunction p f * (Q1 : PowerSeries ℚ)) := by
            simp only [D, Polynomial.coe_mul]; ring
      _ = (C c⁻¹ : PowerSeries ℚ) * (P1 : PowerSeries ℚ) := by rw [hZ1]
      _ = (N : PowerSeries ℚ) := by simp only [N, Polynomial.coe_mul]

private lemma exists_complex_root_of_irreducible {r : ℚ[X]} (hr : Irreducible r) :
    ∃ z : ℂ, aeval z r = 0 := by
  have hdeg : 0 < (r.map (algebraMap ℚ ℂ)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective Rat.cast_injective]
    exact hr.natDegree_pos
  have hdeg' : (r.map (algebraMap ℚ ℂ)).degree ≠ 0 := by
    intro h0
    have := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (r.map (algebraMap ℚ ℂ)) hdeg'
  exact ⟨z, by rwa [Polynomial.aeval_def, ← Polynomial.eval_map]⟩

private lemma weight_inj {q : ℝ} (hq : 1 < q) {i j : ℕ}
    (h : q ^ ((i : ℝ) / 2) = q ^ ((j : ℝ) / 2)) : i = j := by
  have h_eq : ((i : ℝ) / 2) = ((j : ℝ) / 2) := (Real.rpow_right_inj (by linarith) (ne_of_gt hq)).mp h
  have : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast this

private lemma coe_finset_prod_ps {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (((∏ i ∈ s, f i : ℚ[X]) : PowerSeries ℚ)) = ∏ i ∈ s, ((f i : ℚ[X]) : PowerSeries ℚ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Polynomial.coe_mul, ih, Finset.prod_insert ha]

private lemma solve_dim_ge_two (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ C : ℕ → ℚ[X],
      (∀ i ≤ 2 * n, (C i).Monic ∧ (C i).coeff 0 ≠ 0) ∧
      (C 0 = Polynomial.X - 1) ∧
      (zetaFunction p f *
          ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((C i).reverse : ℚ[X]) : PowerSeries ℚ) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((C i).reverse : ℚ[X]) : PowerSeries ℚ)) ∧
      (∀ i ≤ 2 * n,
        (C (2 * n - i)).natDegree = (C i).natDegree ∧
        (C i).coeff 0 • C (2 * n - i) =
          ((C i).comp (Polynomial.C ((Nat.card k : ℚ) ^ n) * Polynomial.X)).reverse) ∧
      (∀ i ≤ 2 * n, ∀ z : ℂ, aeval z (C i) = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  classical
  obtain ⟨N, D, hcop, hN0, hD0, hzeta⟩ :=
    exists_coprime_normalized_zeta p k n X f hproj
  obtain ⟨hrecN, hrecD⟩ :=
    WeilConjectures.zeta_coprime_reciprocity_of_ge_two p k n hn X f hproj N D hcop hN0 hD0 hzeta
  obtain ⟨hX1_dvd, hpurD, hpurN⟩ :=
    WeilConjectures.zeta_coprime_weight_purity_of_ge_two p k n hn X f hproj N D hcop hN0 hD0 hzeta
  let A : ℚ[X] := N.reverse
  let B : ℚ[X] := D.reverse
  have hA_monic : A.Monic := monic_reverse_of_coeff_zero_eq_one hN0
  have hB_monic : B.Monic := monic_reverse_of_coeff_zero_eq_one hD0
  have hN_ne : N ≠ 0 := by intro h0; rw [h0, Polynomial.coeff_zero] at hN0; exact zero_ne_one hN0
  have hD_ne : D ≠ 0 := by intro h0; rw [h0, Polynomial.coeff_zero] at hD0; exact zero_ne_one hD0
  have hA0 : A.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hN_ne
  have hB0 : B.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]; exact Polynomial.leadingCoeff_ne_zero.mpr hD_ne
  have hA_rev : A.reverse = N := reverse_reverse_of_coeff_zero_ne_zero (by rw [hN0]; exact one_ne_zero)
  have hB_rev : B.reverse = D := reverse_reverse_of_coeff_zero_ne_zero (by rw [hD0]; exact one_ne_zero)
  have hq_gt_one : (1 : ℝ) < (Nat.card k : ℝ) := by
    have h2 : 1 < Nat.card k := Finite.one_lt_card
    exact_mod_cast h2
  have hq_pos : (0 : ℝ) < (Nat.card k : ℝ) := by linarith
  let a : ℚ := (Nat.card k : ℚ) ^ n
  have ha_ne : a ≠ 0 := by
    have : 0 < Nat.card k := Nat.card_pos
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt this))
  have hdualA : poincareDual a A = A := by
    unfold poincareDual
    rw [← hrecN, Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hA0,
      map_one, one_mul]
  have hdualB : poincareDual a B = B := by
    unfold poincareDual
    rw [← hrecD, Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hB0,
      map_one, one_mul]
  let fA : Multiset ℚ[X] := UniqueFactorizationMonoid.normalizedFactors A
  let fB : Multiset ℚ[X] := UniqueFactorizationMonoid.normalizedFactors B
  have hmon_prod : ∀ {s : Multiset ℚ[X]}, (∀ r ∈ s, r.Monic) → s.prod.Monic := by
    intro s hs
    simpa using Polynomial.monic_multiset_prod_of_monic s id hs
  have hfA_prod : fA.prod = A := by
    have h := UniqueFactorizationMonoid.prod_normalizedFactors hA_monic.ne_zero
    exact Polynomial.eq_of_monic_of_associated
      (hmon_prod fun r hr => monic_of_mem_normalizedFactors hr) hA_monic h
  have hfB_prod : fB.prod = B := by
    have h := UniqueFactorizationMonoid.prod_normalizedFactors hB_monic.ne_zero
    exact Polynomial.eq_of_monic_of_associated
      (hmon_prod fun r hr => monic_of_mem_normalizedFactors hr) hB_monic h
  let hasWt (i : ℕ) (r : ℚ[X]) : Prop :=
    ∀ z : ℂ, aeval z r = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)
  let Cfun : ℕ → ℚ[X] := fun i =>
    if Even i then (fB.filter (hasWt i)).prod else (fA.filter (hasWt i)).prod
  have hX1_irr : Irreducible (Polynomial.X - 1 : ℚ[X]) :=
    Polynomial.irreducible_X_sub_C 1
  have hX1_monic : (Polynomial.X - 1 : ℚ[X]).Monic := Polynomial.monic_X_sub_C 1
  let B' : ℚ[X] := B / (Polynomial.X - 1)
  have hB_eq : B = (Polynomial.X - 1) * B' :=
    (EuclideanDomain.mul_div_cancel' hX1_monic.ne_zero hX1_dvd).symm
  have hB'_ne : B' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hB_eq; exact hB_monic.ne_zero hB_eq
  have hfB_eq : fB = (Polynomial.X - 1) ::ₘ UniqueFactorizationMonoid.normalizedFactors B' := by
    have hmul := UniqueFactorizationMonoid.normalizedFactors_mul hX1_monic.ne_zero hB'_ne
    rw [← hB_eq, UniqueFactorizationMonoid.normalizedFactors_irreducible hX1_irr,
      hX1_monic.normalize_eq_self, Multiset.singleton_add] at hmul
    exact hmul
  have hfA_wt : ∀ r ∈ fA, ∃ i ∈ (Finset.range (2 * n + 1)).filter Odd, hasWt i r := by
    intro r hr
    have hirr : Irreducible r := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
    have hdvd : r ∣ A := by
      rw [← hfA_prod]; exact Multiset.dvd_prod hr
    obtain ⟨i, hi_le, hi_odd, hwt⟩ := hpurN r hirr hdvd
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le), hi_odd⟩, hwt⟩
  have hfB'_wt : ∀ r ∈ UniqueFactorizationMonoid.normalizedFactors B',
      ∃ i ∈ (Finset.range (2 * n + 1)).filter Even, 0 < i ∧ hasWt i r := by
    intro r hr
    have hirr : Irreducible r := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
    have hdvd : r ∣ B' := by
      have hprod := UniqueFactorizationMonoid.prod_normalizedFactors hB'_ne
      exact dvd_trans (Multiset.dvd_prod hr) hprod.dvd
    obtain ⟨i, hi_le, hi_even, hi_pos, hwt⟩ := hpurD r hirr hdvd
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le), hi_even⟩,
      hi_pos, hwt⟩
  have hfB_wt : ∀ r ∈ fB, ∃ i ∈ (Finset.range (2 * n + 1)).filter Even, hasWt i r := by
    intro r hr
    rw [hfB_eq, Multiset.mem_cons] at hr
    rcases hr with rfl | hr'
    · refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Even.zero⟩, ?_⟩
      intro z hz
      have hz1 : z = 1 := sub_eq_zero.mp (by simpa using hz)
      subst hz1; simp
    · obtain ⟨i, hi, _, hwt⟩ := hfB'_wt r hr'
      exact ⟨i, hi, hwt⟩
  have hwt_unique : ∀ {r : ℚ[X]}, Irreducible r → ∀ {i j : ℕ}, hasWt i r → hasWt j r → i = j := by
    intro r hr i j hi hj
    obtain ⟨z, hz⟩ := exists_complex_root_of_irreducible hr
    exact weight_inj hq_gt_one ((hi z hz).symm.trans (hj z hz))
  have hprod_partition : ∀ (s : Multiset ℚ[X]) (I : Finset ℕ),
      (∀ r ∈ s, Irreducible r) →
      (∀ r ∈ s, ∃ i ∈ I, hasWt i r) →
      ∏ i ∈ I, (s.filter (hasWt i)).prod = s.prod := by
    intro s I hs_irr hs_wt
    induction s using Multiset.induction with
    | empty => simp
    | cons r s ih =>
      have hr_irr := hs_irr r (Multiset.mem_cons_self r s)
      have hs_irr' := fun x hx => hs_irr x (Multiset.mem_cons_of_mem hx)
      have hs_wt' := fun x hx => hs_wt x (Multiset.mem_cons_of_mem hx)
      obtain ⟨i0, hi0, hr_wt⟩ := hs_wt r (Multiset.mem_cons_self r s)
      rw [Multiset.prod_cons, ← ih hs_irr' hs_wt']
      have hterm : ∀ i ∈ I,
          ((r ::ₘ s).filter (hasWt i)).prod =
            (if i = i0 then r else 1) * (s.filter (hasWt i)).prod := by
        intro i _
        by_cases h : i = i0
        · subst h
          rw [Multiset.filter_cons_of_pos _ hr_wt, Multiset.prod_cons, if_pos rfl]
        · have hneg : ¬ hasWt i r := fun hwi => h (hwt_unique hr_irr hwi hr_wt)
          rw [Multiset.filter_cons_of_neg _ hneg, if_neg h, one_mul]
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
        Finset.prod_ite_eq' I i0 (fun _ => r), if_pos hi0]
  have hprod_even : ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, Cfun i = B := by
    have hcongr : ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, Cfun i =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (fB.filter (hasWt i)).prod := by
      refine Finset.prod_congr rfl fun i hi => ?_
      simp [Cfun, (Finset.mem_filter.mp hi).2]
    rw [hcongr, hprod_partition fB _
      (fun r hr => UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr) hfB_wt,
      hfB_prod]
  have hprod_odd : ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, Cfun i = A := by
    have hcongr : ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, Cfun i =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (fA.filter (hasWt i)).prod := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : ¬ Even i := Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp hi).2
      simp [Cfun, hne]
    rw [hcongr, hprod_partition fA _
      (fun r hr => UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr) hfA_wt,
      hfA_prod]
  have hf_dual : ∀ (P : ℚ[X]) (hP : P.Monic) (hP0 : P.coeff 0 ≠ 0) (hPdual : poincareDual a P = P),
      (UniqueFactorizationMonoid.normalizedFactors P).map (poincareDual a) =
        UniqueFactorizationMonoid.normalizedFactors P := by
    intro P hP hP0 hPdual
    let s := UniqueFactorizationMonoid.normalizedFactors P
    have hs_prod : s.prod = P :=
      Polynomial.eq_of_monic_of_associated
        (hmon_prod fun r hr => monic_of_mem_normalizedFactors hr)
        hP (UniqueFactorizationMonoid.prod_normalizedFactors hP.ne_zero)
    have hs_r0 : ∀ r ∈ s, r.coeff 0 ≠ 0 := by
      intro r hr h0
      have hdvd : r ∣ P := by rw [← hs_prod]; exact Multiset.dvd_prod hr
      rcases hdvd with ⟨q, hq⟩
      have := congrArg (fun p : ℚ[X] => p.coeff 0) hq
      rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
      exact hP0 this
    have hmap_irr : ∀ u ∈ s.map (poincareDual a), Irreducible u := by
      intro u hu
      rw [Multiset.mem_map] at hu
      obtain ⟨r, hr, rfl⟩ := hu
      exact poincareDual_irreducible ha_ne (monic_of_mem_normalizedFactors hr) (hs_r0 r hr)
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr)
    have hmap_norm : (s.map (poincareDual a)).map normalize = s.map (poincareDual a) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun r hr => ?_
      exact (poincareDual_monic ha_ne (hs_r0 r hr)).normalize_eq_self
    have hmap_prod : (s.map (poincareDual a)).prod = P := by
      rw [← poincareDual_multiset_prod, hs_prod, hPdual]
    have hnf := UniqueFactorizationMonoid.normalizedFactors_prod_eq (s.map (poincareDual a)) hmap_irr
    rw [hmap_prod, hmap_norm] at hnf
    exact hnf.symm
  have hfA_dual : fA.map (poincareDual a) = fA := hf_dual A hA_monic hA0 hdualA
  have hfB_dual : fB.map (poincareDual a) = fB := hf_dual B hB_monic hB0 hdualB
  have hwt_dual : ∀ {r : ℚ[X]} {i : ℕ} (hi : i ≤ 2 * n),
      r.Monic → r.coeff 0 ≠ 0 → (hasWt (2 * n - i) (poincareDual a r) ↔ hasWt i r) := by
    intro r i hi hr_monic hr0
    have hpow_split : (Nat.card k : ℝ) ^ (n : ℝ) / (Nat.card k : ℝ) ^ ((i : ℝ) / 2) =
        (Nat.card k : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) := by
      rw [← Real.rpow_sub hq_pos]
      congr 1
      rw [Nat.cast_sub hi, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hpow_split' : (Nat.card k : ℝ) ^ (n : ℝ) / (Nat.card k : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) =
        (Nat.card k : ℝ) ^ ((i : ℝ) / 2) := by
      rw [← Real.rpow_sub hq_pos]
      congr 1
      rw [Nat.cast_sub hi, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have ha_norm : ‖(a : ℂ)‖ = (Nat.card k : ℝ) ^ (n : ℝ) := by
      simp only [a, Rat.cast_pow, Rat.cast_natCast, norm_pow, Complex.norm_natCast, Real.rpow_natCast]
    constructor
    · intro hdual w hw
      have hw_ne : w ≠ 0 := by
        intro h0; subst h0
        have : aeval (0 : ℂ) r = (r.coeff 0 : ℂ) := by
          simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
        rw [this] at hw
        exact hr0 (Rat.cast_injective (α := ℂ) (by simpa using hw))
      have haC_ne : (a : ℂ) ≠ 0 := by exact_mod_cast ha_ne
      let z : ℂ := (a : ℂ) / w
      have hz_ne : z ≠ 0 := div_ne_zero haC_ne hw_ne
      have hz_root : aeval z (poincareDual a r) = 0 := by
        rw [aeval_poincareDual_eq_zero_iff ha_ne hr_monic hr0 z]
        refine ⟨hz_ne, ?_⟩
        have hdiv : (a : ℂ) / z = w := by
          simp only [z]
          exact div_div_cancel₀ haC_ne
        rwa [hdiv]
      have hz_norm := hdual z hz_root
      have hzn : ‖(a : ℂ)‖ / ‖w‖ = (Nat.card k : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) := by
        simpa [z, norm_div] using hz_norm
      have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
      have hrhs_pos : 0 < (Nat.card k : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos hq_pos _
      rw [ha_norm] at hzn
      have : ‖w‖ = (Nat.card k : ℝ) ^ (n : ℝ) / (Nat.card k : ℝ) ^ (((2 * n - i : ℕ) : ℝ) / 2) := by
        rw [eq_div_iff (ne_of_gt hrhs_pos)]
        have := (div_eq_iff (ne_of_gt hw_pos)).mp hzn
        linarith
      rw [this, hpow_split']
    · intro hr_wt z hz
      rw [aeval_poincareDual_eq_zero_iff ha_ne hr_monic hr0 z] at hz
      obtain ⟨hz_ne, hroot⟩ := hz
      have hwn := hr_wt ((a : ℂ) / z) hroot
      rw [norm_div, ha_norm] at hwn
      have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      have hrhs_pos : 0 < (Nat.card k : ℝ) ^ ((i : ℝ) / 2) := Real.rpow_pos_of_pos hq_pos _
      have : ‖z‖ = (Nat.card k : ℝ) ^ (n : ℝ) / (Nat.card k : ℝ) ^ ((i : ℝ) / 2) := by
        rw [eq_div_iff (ne_of_gt hrhs_pos)]
        have := (div_eq_iff (ne_of_gt hz_pos)).mp hwn
        linarith
      rw [this, hpow_split]
  have hC_monic_c0 : ∀ i ≤ 2 * n, (Cfun i).Monic ∧ (Cfun i).coeff 0 ≠ 0 := by
    intro i _
    by_cases he : Even i
    · have hCi : Cfun i = (fB.filter (hasWt i)).prod := by simp [Cfun, he]
      rw [hCi]
      refine ⟨hmon_prod fun r hr =>
        monic_of_mem_normalizedFactors (Multiset.mem_of_mem_filter hr), ?_⟩
      intro h0
      have hdvd : (fB.filter (hasWt i)).prod ∣ B := by
        rw [← hfB_prod]
        exact Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)
      rcases hdvd with ⟨q, hq⟩
      have := congrArg (fun p : ℚ[X] => p.coeff 0) hq
      rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
      exact hB0 this
    · have hCi : Cfun i = (fA.filter (hasWt i)).prod := by simp [Cfun, he]
      rw [hCi]
      refine ⟨hmon_prod fun r hr =>
        monic_of_mem_normalizedFactors (Multiset.mem_of_mem_filter hr), ?_⟩
      intro h0
      have hdvd : (fA.filter (hasWt i)).prod ∣ A := by
        rw [← hfA_prod]
        exact Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)
      rcases hdvd with ⟨q, hq⟩
      have := congrArg (fun p : ℚ[X] => p.coeff 0) hq
      rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
      exact hA0 this
  refine ⟨Cfun, hC_monic_c0, ?_, ?_, ?_, ?_⟩
  · have hC0 : Cfun 0 = (fB.filter (hasWt 0)).prod := by simp [Cfun]
    rw [hC0, hfB_eq]
    have hX1_wt0 : hasWt 0 (Polynomial.X - 1) := by
      intro z hz
      have hz1 : z = 1 := sub_eq_zero.mp (by simpa using hz)
      subst hz1; simp
    have hB'_no0 : (UniqueFactorizationMonoid.normalizedFactors B').filter (hasWt 0) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro r hr hwt0
      obtain ⟨i, _, hi_pos, hwti⟩ := hfB'_wt r hr
      have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr
      have hi0 := hwt_unique hirr hwt0 hwti
      omega
    rw [Multiset.filter_cons_of_pos _ hX1_wt0, hB'_no0, Multiset.prod_cons, Multiset.prod_zero,
      mul_one]
  · have hev_rev :
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((Cfun i).reverse : ℚ[X]) : PowerSeries ℚ) =
          (D : PowerSeries ℚ) := by
      rw [← coe_finset_prod_ps, ← reverse_finset_prod, hprod_even, hB_rev]
    have hodd_rev :
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((Cfun i).reverse : ℚ[X]) : PowerSeries ℚ) =
          (N : PowerSeries ℚ) := by
      rw [← coe_finset_prod_ps, ← reverse_finset_prod, hprod_odd, hA_rev]
    rw [hev_rev, hodd_rev]
    exact hzeta
  · intro i hi
    have hC_dual : poincareDual a (Cfun i) = Cfun (2 * n - i) := by
      have hpar : Even (2 * n - i) ↔ Even i := by
        rw [Nat.even_sub hi]
        simp [even_two]
      by_cases he : Even i
      · have he' : Even (2 * n - i) := hpar.mpr he
        simp only [Cfun, if_pos he, if_pos he']
        rw [poincareDual_multiset_prod]
        congr 1
        have hr0_fB : ∀ r ∈ fB, r.coeff 0 ≠ 0 := by
          intro r hr h0
          have hdvd : r ∣ B := by rw [← hfB_prod]; exact Multiset.dvd_prod hr
          rcases hdvd with ⟨q, hq⟩
          have := congrArg (fun p : ℚ[X] => p.coeff 0) hq
          rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
          exact hB0 this
        calc
          (fB.filter (hasWt i)).map (poincareDual a)
              = (fB.filter (fun r => hasWt (2 * n - i) (poincareDual a r))).map (poincareDual a) := by
                congr 1
                refine Multiset.filter_congr fun r hr => ?_
                exact (hwt_dual hi (monic_of_mem_normalizedFactors hr) (hr0_fB r hr)).symm
          _ = (fB.map (poincareDual a)).filter (hasWt (2 * n - i)) :=
                (Multiset.filter_map (hasWt (2 * n - i)) (poincareDual a) fB).symm
          _ = fB.filter (hasWt (2 * n - i)) := by rw [hfB_dual]
      · have he' : ¬ Even (2 * n - i) := fun h => he (hpar.mp h)
        simp only [Cfun, if_neg he, if_neg he']
        rw [poincareDual_multiset_prod]
        congr 1
        have hr0_fA : ∀ r ∈ fA, r.coeff 0 ≠ 0 := by
          intro r hr h0
          have hdvd : r ∣ A := by rw [← hfA_prod]; exact Multiset.dvd_prod hr
          rcases hdvd with ⟨q, hq⟩
          have := congrArg (fun p : ℚ[X] => p.coeff 0) hq
          rw [Polynomial.mul_coeff_zero, h0, zero_mul] at this
          exact hA0 this
        calc
          (fA.filter (hasWt i)).map (poincareDual a)
              = (fA.filter (fun r => hasWt (2 * n - i) (poincareDual a r))).map (poincareDual a) := by
                congr 1
                refine Multiset.filter_congr fun r hr => ?_
                exact (hwt_dual hi (monic_of_mem_normalizedFactors hr) (hr0_fA r hr)).symm
          _ = (fA.map (poincareDual a)).filter (hasWt (2 * n - i)) :=
                (Multiset.filter_map (hasWt (2 * n - i)) (poincareDual a) fA).symm
          _ = fA.filter (hasWt (2 * n - i)) := by rw [hfA_dual]
    have hCi0 : (Cfun i).coeff 0 ≠ 0 := (hC_monic_c0 i hi).2
    refine ⟨?_, ?_⟩
    · rw [← hC_dual, poincareDual_natDegree ha_ne hCi0]
    · rw [← hC_dual]
      unfold poincareDual
      rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hCi0,
        map_one, one_mul]
  · intro i _ z hz
    by_cases he : Even i
    · have hCi : Cfun i = (fB.filter (hasWt i)).prod := by simp [Cfun, he]
      rw [hCi, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
      obtain ⟨r, hr, hz0⟩ := hz
      exact le_of_eq ((Multiset.mem_filter.mp hr).2 z hz0)
    · have hCi : Cfun i = (fA.filter (hasWt i)).prod := by simp [Cfun, he]
      rw [hCi, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
      obtain ⟨r, hr, hz0⟩ := hz
      exact le_of_eq ((Multiset.mem_filter.mp hr).2 z hz0)

end DimGeTwo

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ C : ℕ → ℚ[X],
      (∀ i ≤ 2 * n, (C i).Monic ∧ (C i).coeff 0 ≠ 0) ∧
      (C 0 = Polynomial.X - 1) ∧
      (zetaFunction p f *
          ∏ i ∈ (Finset.range (2 * n + 1)).filter Even, (((C i).reverse : ℚ[X]) : PowerSeries ℚ) =
        ∏ i ∈ (Finset.range (2 * n + 1)).filter Odd, (((C i).reverse : ℚ[X]) : PowerSeries ℚ)) ∧
      (∀ i ≤ 2 * n,
        (C (2 * n - i)).natDegree = (C i).natDegree ∧
        (C i).coeff 0 • C (2 * n - i) =
          ((C i).comp (Polynomial.C ((Nat.card k : ℚ) ^ n) * Polynomial.X)).reverse) ∧
      (∀ i ≤ 2 * n, ∀ z : ℂ, aeval z (C i) = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  rcases n with _ | _ | m
  · exact solve_dim_zero p k X f hproj
  · exact solve_dim_one p k X f hproj
  · exact solve_dim_ge_two p k (m + 2) (by omega) X f hproj
