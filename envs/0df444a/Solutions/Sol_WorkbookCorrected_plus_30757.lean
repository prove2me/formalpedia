-- Prove2me | solution 1 for WorkbookCorrected.plus_30757
-- status  : ACCEPTED   (prove)
-- author  : @yerui
-- created : 2026-09-30T05:39:51.860352+00:00
-- url     : https://prove2.me/submissions/5046a9ba-fab6-41f1-a10d-42d4c223635a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem solution : (Real.logb 2 9) * (Real.logb 3 7) * (Real.logb 7 8) = 6 := by
  rw [Real.logb, Real.logb, Real.logb]
  rw [show (9:ℝ) = 3^2 by norm_num, show (8:ℝ) = 2^3 by norm_num]
  rw [Real.log_pow, Real.log_pow]
  norm_num
  field_simp
  ring
