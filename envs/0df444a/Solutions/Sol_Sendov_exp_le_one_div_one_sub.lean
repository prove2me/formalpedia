-- Prove2me | solution 1 for Sendov.exp_le_one_div_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:09.001664+00:00
-- url     : https://prove2.me/submissions/dae46a85-f77c-4ea1-8a50-23eec35bca46

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17

set_option autoImplicit false
open Sendov
open MeasureTheory Real
namespace Sendov
theorem _root_.solution {z : ℝ} (hz : z < 1) : exp z ≤ 1 / (1 - z) := by
  have hpos := Real.exp_pos z
  have h1 : (0 : ℝ) < 1 - z := by linarith
  have h := Real.add_one_le_exp (-z)
  rw [Real.exp_neg] at h
  have h2 : (1 - z) * exp z ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  rw [le_div_iff₀ h1]
  linarith
end Sendov
