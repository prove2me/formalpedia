-- Prove2me | solution 1 for Sendov.log_seventeen_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:11.88312+00:00
-- url     : https://prove2.me/submissions/a08ffb39-b9e1-43ef-937e-ecdd6c3e4be0

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17

set_option autoImplicit false
open Sendov
open MeasureTheory Real
namespace Sendov
theorem _root_.solution : (2.83 : ℝ) ≤ Real.log 17 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hfrac : (1 : ℝ) - 16 / 17 ≤ Real.log (17 / 16) := by
    have h := Real.log_le_sub_one_of_pos (x := (16 : ℝ) / 17) (by norm_num)
    rw [show (16 : ℝ) / 17 = ((17 : ℝ) / 16)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hsplit : Real.log 17 = Real.log 16 + Real.log (17 / 16) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit, h16]
  linarith
end Sendov
