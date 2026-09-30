-- Prove2me | solution 1 for WorkbookCorrected.plus_82892
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:08:00.820493+00:00
-- url     : https://prove2.me/submissions/aeea24da-c696-4385-aace-c4c6b762a87d

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 2 3 > Real.logb 3 2 := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h3 : (0:ℝ) < Real.log 3 := lt_trans h2 h23
  have hsq : (Real.log 2) ^ 2 < (Real.log 3) ^ 2 := sq_lt_sq' (by linarith) h23
  unfold Real.logb
  rw [gt_iff_lt, div_lt_div_iff₀ h3 h2]
  linear_combination hsq
