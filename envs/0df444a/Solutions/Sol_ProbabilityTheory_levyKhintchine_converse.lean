-- Prove2me | solution 1 for ProbabilityTheory.levyKhintchine_converse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:33:25.659772+00:00
-- url     : https://prove2.me/submissions/e845c4b7-381a-4695-a5a3-327ffda9cffc

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_continuous
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_zero
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_cnd
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_hermitian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Original converse Lévy-Khintchine theorem from the pinned source. -/
theorem solution (T : LevyKhintchineTriple) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  set S := convolutionSemigroupOfCND T.exponent_continuous T.exponent_zero
    T.exponent_cnd T.exponent_hermitian with hS
  have hcf : ∀ (t : {t : ℝ // 0 < t}) (ξ : ℝ),
      charFun (S.measure t : Measure ℝ) ξ = Complex.exp ((↑t.val : ℂ) * T.exponent ξ) :=
    fun t ξ => S.charFun_eq t ξ
  refine ⟨(S.measure ⟨1, one_pos⟩ : Measure ℝ), inferInstance, ?_, ?_⟩
  · intro n hn
    have hnpos : (0 : ℝ) < 1 / n := div_pos one_pos (Nat.cast_pos.mpr hn)
    refine ⟨(S.measure ⟨1 / n, hnpos⟩ : Measure ℝ), inferInstance, ?_⟩
    apply Measure.ext_of_charFun
    funext ξ
    rw [Measure.charFun_iteratedConv, hcf ⟨1 / n, hnpos⟩ ξ, hcf ⟨1, one_pos⟩ ξ,
      ← Complex.exp_nat_mul]
    congr 1
    have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_one, one_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · intro ξ
    rw [hcf ⟨1, one_pos⟩ ξ]
    simp only [Complex.ofReal_one, one_mul]
