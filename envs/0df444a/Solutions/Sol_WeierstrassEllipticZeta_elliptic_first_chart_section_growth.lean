-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_first_chart_section_growth
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T14:23:00.781763+00:00
-- url     : https://prove2.me/submissions/5966c451-e485-411f-921a-4ad0904fa134

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_section_dimension
import Theorems.Thm_TranscendenceTheory_bihomogeneous_lift_four_variables
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial TranscendenceTheory

private lemma cubic_y_degree (L : PeriodPair) :
    (extensionChartCubic L.g₂ L.g₃ 0).degreeOf (2 : Fin 4) = 2 := by
  let q : MvPolynomial (Fin 4) ℂ :=
    -(C 4 * X 1 ^ 3) + C L.g₂ * X 1 + C L.g₃
  have hq : q.degreeOf 2 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_add_le 2 _ _).trans
    apply max_le _ (by simp)
    apply (degreeOf_add_le 2 _ _).trans
    apply max_le
    · rw [degreeOf_neg]
      exact (degreeOf_C_mul_le _ _ _).trans_eq (degreeOf_X_pow_of_ne 3 (by decide))
    · exact (degreeOf_C_mul_le _ _ _).trans_eq (degreeOf_X_of_ne (by decide))
  have heq : extensionChartCubic L.g₂ L.g₃ 0 = X 2 ^ 2 + q := by
    simp only [extensionChartCubic, q, if_true]
    ring
  rw [heq, degreeOf_add_eq_of_degreeOf_lt (by simp [hq])]
  exact degreeOf_X_self_pow 2 2

private lemma reduced_quotient_injective (L : PeriodPair)
    (P : MvPolynomial (Fin 4) ℂ) (hP : P.degreeOf 2 ≤ 1)
    (hz : firstCubicQuotient L P = 0) : P = 0 := by
  have hmem : P ∈ Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp hmem
  by_cases hzero : H = 0
  · simpa [hzero] using hH
  have hc : extensionChartCubic L.g₂ L.g₃ 0 ≠ 0 := by
    intro h
    have hd := cubic_y_degree L
    rw [h, degreeOf_zero] at hd
    omega
  have hd := degreeOf_mul_eq (n := (2 : Fin 4)) hc hzero
  rw [← hH, cubic_y_degree L] at hd
  omega

/-- A square indexes the degree-n normal monomials: its lower triangle has no
 y factor; reflection of the upper triangle supplies the terms with one y. -/
private def sectionExponent (m n : ℕ)
    (a : Fin (m + 1) × Fin (n + 1) × Fin (n + 1)) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (if a.2.1.val + a.2.2.val ≤ n then
      ![a.1.val, a.2.1.val, 0, a.2.2.val]
    else ![a.1.val, n - a.2.1.val, 1, n - a.2.2.val])

private lemma sectionExponent_bounds (m n : ℕ)
    (a : Fin (m + 1) × Fin (n + 1) × Fin (n + 1)) :
    sectionExponent m n a 0 ≤ m ∧
    sectionExponent m n a 1 + sectionExponent m n a 2 + sectionExponent m n a 3 ≤ n ∧
    sectionExponent m n a 2 ≤ 1 := by
  have hi := a.1.isLt
  have hj := a.2.1.isLt
  have hk := a.2.2.isLt
  by_cases h : a.2.1.val + a.2.2.val ≤ n <;> simp [sectionExponent, h] <;> omega

private lemma sectionExponent_injective (m n : ℕ) :
    Function.Injective (sectionExponent m n) := by
  intro a b hab
  have h0 := DFunLike.congr_fun hab 0
  have h1 := DFunLike.congr_fun hab 1
  have h2 := DFunLike.congr_fun hab 2
  have h3 := DFunLike.congr_fun hab 3
  have ha1 := a.2.1.isLt
  have ha2 := a.2.2.isLt
  have hb1 := b.2.1.isLt
  have hb2 := b.2.2.isLt
  by_cases ha : a.2.1.val + a.2.2.val ≤ n <;>
    by_cases hb : b.2.1.val + b.2.2.val ≤ n <;>
    simp [sectionExponent, ha, hb] at h0 h1 h2 h3
  all_goals
    apply Prod.ext
    · exact Fin.ext h0
    · apply Prod.ext <;> apply Fin.ext <;> omega

private lemma bounded_polynomial_is_section (L : PeriodPair)
    (P : MvPolynomial (Fin 4) ℂ) (m n : ℕ)
    (hP : ∀ d ∈ P.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ n) :
    firstCubicQuotient L P ∈ firstChartSectionSpace L m n := by
  obtain ⟨Q, hQ, heval⟩ := bihomogeneous_lift_four_variables ℂ P m n hP
  have hnormalize : extensionChartNormalize 0 Q = P := by
    apply MvPolynomial.funext
    intro x
    have hx := heval x 1 1 (x 2 * x 3 + 2 * x 1 ^ 2)
    change (aeval x) ((aeval (extensionChartSubstitution 0)) Q) = _
    rw [comp_aeval_apply]
    have hv : (fun i => aeval x (extensionChartSubstitution 0 i)) =
        ![1, x 0, 1, x 1, x 2, x 3, x 2 * x 3 + 2 * x 1 ^ 2] := by
      funext i
      fin_cases i <;> simp [extensionChartSubstitution]
    rw [hv]
    simpa only [one_mul, one_pow, mul_one, aeval_eq_eval] using hx
  exact Submodule.subset_span ⟨Q, fun d hd => ⟨(hQ d hd).1, (hQ d hd).2.1⟩,
    congrArg (firstCubicQuotient L) hnormalize⟩

private lemma normal_sections_independent (L : PeriodPair) (m n : ℕ) :
    LinearIndependent ℂ (fun a : Fin (m + 1) × Fin (n + 1) × Fin (n + 1) =>
      firstCubicQuotient L (monomial (sectionExponent m n a) (1 : ℂ))) := by
  classical
  have hbase : LinearIndependent ℂ
      (fun a : Fin (m + 1) × Fin (n + 1) × Fin (n + 1) =>
        monomial (sectionExponent m n a) (1 : ℂ)) := by
    simpa only [coe_basisMonomials, Function.comp_def] using
      (basisMonomials (Fin 4) ℂ).linearIndependent.comp
        (sectionExponent m n) (sectionExponent_injective m n)
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp hbase c
  apply reduced_quotient_injective L
  · apply (degreeOf_sum_le 2 Finset.univ _).trans
    apply Finset.sup_le
    intro a _
    rw [smul_monomial]
    apply degreeOf_le_iff.mpr
    intro d hd
    rw [Finset.mem_singleton.mp (support_monomial_subset hd)]
    exact (sectionExponent_bounds m n a).2.2
  · simpa only [map_sum, map_smul] using hc

private lemma section_dimension_lower (L : PeriodPair) (m n : ℕ) :
    (m + 1) * (n + 1) ^ 2 ≤ Module.finrank ℂ (firstChartSectionSpace L m n) := by
  classical
  let : Module.Finite ℂ (firstChartSectionSpace L m n) :=
    (elliptic_first_chart_section_dimension L m n).1
  have hmem (a : Fin (m + 1) × Fin (n + 1) × Fin (n + 1)) :
      firstCubicQuotient L (monomial (sectionExponent m n a) (1 : ℂ)) ∈
        firstChartSectionSpace L m n := by
    apply bounded_polynomial_is_section
    intro d hd
    have he : d = sectionExponent m n a :=
      Finset.mem_singleton.mp (support_monomial_subset hd)
    subst d
    exact ⟨(sectionExponent_bounds m n a).1, (sectionExponent_bounds m n a).2.1⟩
  let f : (Fin (m + 1) × Fin (n + 1) × Fin (n + 1)) → firstChartSectionSpace L m n :=
    fun a => ⟨_, hmem a⟩
  have hf : LinearIndependent ℂ f :=
    LinearIndependent.of_comp (firstChartSectionSpace L m n).subtype
      (normal_sections_independent L m n)
  have hdim := hf.fintype_card_le_finrank
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hdim


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (m n : ℕ) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    (m + 1) * (n + 1) ^ 2 ≤ Module.finrank ℂ (firstChartSectionSpace L m n) ∧
    (1 ≤ n → Module.finrank ℂ (firstChartSectionSpace L m n) ≤
      30 * (m + 1) * n ^ 2) := by
  exact ⟨(elliptic_first_chart_section_dimension L m n).1,
    section_dimension_lower L m n, (elliptic_first_chart_section_dimension L m n).2.2⟩
