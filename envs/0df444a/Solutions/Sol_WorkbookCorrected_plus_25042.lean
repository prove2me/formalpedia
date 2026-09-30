-- Prove2me | solution 1 for WorkbookCorrected.plus_25042
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:44:44.016795+00:00
-- url     : https://prove2.me/submissions/478e5a8b-237f-4e09-a086-2fbf79de6964

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 2 (Real.logb 4 16) = 1 := by
  have h16 : (16 : ℝ) = 4 ^ 2 := by norm_num
  have h1 : Real.logb 4 16 = 2 := by
    rw [h16, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [h1]
  exact Real.logb_self_eq_one (by norm_num)
