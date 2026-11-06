-- Prove2me | solution 1 for ProbabilityTheory.norm_levyCompensatedIntegrand_le_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:19:15.350726+00:00
-- url     : https://prove2.me/submissions/1345a0b4-126c-43ac-b0b7-08def256ede7

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory Complex Set

theorem solution {ξ x : ℝ} (hx : 1 ≤ |x|) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ 2 := by
  simp only [levyCompensatedIntegrand, not_lt.mpr hx, if_false, mul_zero, sub_zero]
  calc ‖exp (↑x * ↑ξ * I) - 1‖
      ≤ ‖exp (↑x * ↑ξ * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
        rw [show (↑x : ℂ) * ↑ξ * I = ↑(x * ξ) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, norm_one]
    _ = 2 := by ring
