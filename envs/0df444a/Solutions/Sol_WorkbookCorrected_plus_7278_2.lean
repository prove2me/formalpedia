-- Prove2me | solution 2 for WorkbookCorrected.plus_7278
-- status  : ACCEPTED   (prove)
-- author  : @yerui
-- created : 2026-09-30T05:54:16.94821+00:00
-- url     : https://prove2.me/submissions/6a4a0087-1b0b-4836-8b53-bce4641d1438

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem solution : 8 ^ Real.logb 2 (Real.sqrt 6) = 6 * Real.sqrt 6 := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have h6 : (0:ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, ← Real.rpow_natCast 2 3]
  rw [← Real.rpow_mul (le_of_lt h2)]
  rw [mul_comm]
  rw [Real.rpow_mul (le_of_lt h2)]
  rw [Real.rpow_logb h2 (by norm_num) h6]
  rw [Real.rpow_natCast]
  calc (Real.sqrt 6)^3 = (Real.sqrt 6)^2 * Real.sqrt 6 := by ring
    _ = 6 * Real.sqrt 6 := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
