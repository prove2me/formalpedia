-- Prove2me | solution 1 for ProbabilityTheory.continuous_levyCompensatedIntegrand_fst
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:23:45.119316+00:00
-- url     : https://prove2.me/submissions/a131fdce-e456-417f-86e5-a0cf26e6bdd7

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

theorem solution (x : ℝ) :
    Continuous (fun ξ => levyCompensatedIntegrand ξ x) := by
  unfold levyCompensatedIntegrand
  by_cases hx : |x| < 1
  · simp only [if_pos hx, mul_one]
    fun_prop
  · simp only [if_neg hx, mul_zero, sub_zero]
    fun_prop
