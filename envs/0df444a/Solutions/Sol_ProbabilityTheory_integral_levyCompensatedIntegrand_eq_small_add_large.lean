-- Prove2me | solution 1 for ProbabilityTheory.integral_levyCompensatedIntegrand_eq_small_add_large
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:37:11.733504+00:00
-- url     : https://prove2.me/submissions/8b375b9a-6cb7-4799-bac7-be2fb5ab4b60

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) (ξ : ℝ) :
    ∫ x, levyCompensatedIntegrand ξ x ∂ν
      = (∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν)
        + ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν := by
  have hcompl : (Set.Ioo (-1 : ℝ) 1)ᶜ = {x : ℝ | 1 ≤ |x|} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_setOf_eq]
    constructor
    · rintro (h | h)
      · exact le_trans (by linarith) (neg_le_abs x)
      · exact le_trans h (le_abs_self x)
    · intro h
      rcases le_total 0 x with hx | hx
      · right
        rwa [abs_of_nonneg hx] at h
      · left
        rw [abs_of_nonpos hx] at h
        linarith
  rw [← integral_add_compl measurableSet_Ioo (integrable_levyCompensatedIntegrand hν ξ)]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    rw [Set.mem_Ioo] at hx
    simp only [levyCompensatedIntegrand, abs_lt.mpr hx, if_true, mul_one]
  · rw [hcompl]
    apply setIntegral_congr_fun (hcompl ▸ measurableSet_Ioo.compl)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [levyCompensatedIntegrand, not_lt.mpr hx, if_false, mul_zero, sub_zero]
