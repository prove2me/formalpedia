-- Prove2me | solution 1 for WorkbookCorrected.plus_2050
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T06:43:33.698694+00:00
-- url     : https://prove2.me/submissions/24166ecb-57ca-424a-97f9-d252f9be8057

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

theorem solution : Real.log 5 / Real.log 3 * (Real.log 7 / Real.log 5) = Real.log 7 / Real.log 3 := by
  have ha : Real.log 5 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hc : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp [ha, hc]
