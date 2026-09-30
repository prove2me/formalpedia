-- Prove2me | solution 1 for WorkbookCorrected.plus_59205
-- status  : ACCEPTED   (disprove)
-- author  : @Sneed
-- created : 2026-09-30T09:06:05.01305+00:00
-- url     : https://prove2.me/submissions/d860d6bb-1c65-4791-9e4e-265f6a6fe127

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem solution : ¬ (Real.log 2 > (2/5) ^ (2/5)) := by
  have h : Real.log 2 < 1 := by
    have h' := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h' ⊢
    exact h'
  norm_num
  linarith
