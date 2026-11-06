-- Prove2me | solution 1 for ProbabilityTheory.conj_levyCompensatedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:20:35.176054+00:00
-- url     : https://prove2.me/submissions/e284bec7-379a-40a5-88f3-4b2c54d22f08

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory Complex Set

theorem solution (ξ x : ℝ) :
    starRingEnd ℂ (levyCompensatedIntegrand ξ x) = levyCompensatedIntegrand (-ξ) x := by
  have hww : starRingEnd ℂ ((↑x : ℂ) * ↑ξ * I) = (↑x : ℂ) * ↑(-ξ) * I := by
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  simp only [levyCompensatedIntegrand]
  by_cases hx : |x| < 1
  · simp only [if_pos hx, mul_one, map_sub, map_one, ← exp_conj, hww]
  · simp only [if_neg hx, mul_zero, sub_zero, map_sub, map_one, ← exp_conj, hww]
