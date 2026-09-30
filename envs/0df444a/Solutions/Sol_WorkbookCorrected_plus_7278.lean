-- Prove2me | solution 1 for WorkbookCorrected.plus_7278
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:49:16.245984+00:00
-- url     : https://prove2.me/submissions/c02938b9-1f3f-43f5-a9e7-7aff19f516d3

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : 8 ^ Real.logb 2 (Real.sqrt 6) = 6 * Real.sqrt 6 := by
  calc
    (8 : ℝ) ^ Real.logb 2 (Real.sqrt 6) =
        ((2 : ℝ) ^ (3 : ℝ)) ^ Real.logb 2 (Real.sqrt 6) := by norm_num
    _ = ((2 : ℝ) ^ Real.logb 2 (Real.sqrt 6)) ^ (3 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
        ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_comm]
    _ = Real.sqrt 6 ^ 3 := by
      rw [Real.rpow_logb (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1)
        (Real.sqrt_pos.2 (by norm_num : 0 < (6 : ℝ)))]
      norm_num [Real.rpow_natCast]
    _ = 6 * Real.sqrt 6 := by
      rw [pow_succ, Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ))]

