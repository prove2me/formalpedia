-- Prove2me | solution 1 for Sendov.tail_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:25.786422+00:00
-- url     : https://prove2.me/submissions/d94f1c73-0a06-4664-af65-c6b19841ad7f

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17
import Theorems.Thm_Sendov_quartic_le_exp

set_option autoImplicit false
open Sendov
open MeasureTheory Real
namespace Sendov
theorem _root_.solution {v : ℝ} (hv : 0 ≤ v) :
    v * (2 * (v + 1) + 1 / 17) * exp (-(2.83 * v)) ≤ 0.4118 := by
  have hz : (0 : ℝ) ≤ 2.83 * v := by linarith
  have hexp := quartic_le_exp hz
  have hpos : (0 : ℝ) < exp (2.83 * v) := Real.exp_pos _
  have hneg : exp (-(2.83 * v)) = (exp (2.83 * v))⁻¹ := Real.exp_neg _
  rw [hneg, mul_inv_le_iff₀ hpos]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 0.4118))
  nlinarith [hv, sq_nonneg v, sq_nonneg (v - 1 / 2), pow_nonneg hv 3]
end Sendov
