-- Prove2me | solution 1 for WorkbookCorrected.plus_23480
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:54:48.574056+00:00
-- url     : https://prove2.me/submissions/364661ad-dab6-4fa0-aabd-299804dcf268

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 4 8 = 3 / 2 := by
  have h4 : Real.log 4 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  -- logb 4 8 = log 8 / log 4
  rw [Real.logb]
  -- log 8 = log (2^3) = 3 log 2, log 4 = log (2^2) = 2 log 2
  have h2pos : (0:ℝ) < 2 := by norm_num
  have h8 : Real.log 8 = Real.log (2^3) := by norm_num
  have h4e : Real.log 4 = Real.log (2^2) := by norm_num
  rw [show (8:ℝ) = 2^3 by norm_num, show (4:ℝ) = 2^2 by norm_num]
  rw [Real.log_pow, Real.log_pow]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one h2pos (by norm_num : (2:ℝ) ≠ 1)]
  ring
