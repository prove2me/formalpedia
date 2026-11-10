-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:40:20.07792+00:00
-- url     : https://prove2.me/submissions/e72a20fe-2deb-400f-bcc7-3161fd68a8ad

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_exp_I_taylor3_bound_public
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Source-exact cubic remainder bound from the characteristic-exponent expansion. -/
theorem solution
    {ξ x : ℝ} (hxξ : |x * ξ| ≤ 1) :
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
      + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 := by
  have h := ProbabilityTheory.leanlevy_chat31_exp_I_taylor3_bound_public (z := x * ξ) hxξ
  have heq : exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I +
        ((↑x : ℂ) * ↑ξ) ^ 2 / 2 =
      Complex.exp ((↑(x * ξ) : ℂ) * I) - 1 -
        (↑(x * ξ) : ℂ) * I + (↑(x * ξ) : ℂ) ^ 2 / 2 := by
    push_cast
    ring
  rw [heq]
  refine h.trans (le_of_eq ?_)
  rw [abs_mul, mul_pow]
  ring
