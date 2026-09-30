-- Prove2me | solution 1 for WorkbookCorrected.plus_27624
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:15:18.579+00:00
-- url     : https://prove2.me/submissions/86959242-4499-4d4d-a386-9c5f7adaf5e6

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

theorem solution : (Real.logb 2 3) * (Real.logb 3 4) * (Real.logb 4 5) * (Real.logb 5 6) = Real.logb 2 6 := by
  -- change of base: product telescopes to log 6 / log 2
  simp only [Real.logb]
  have h2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h4 : Real.log 4 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h5 : Real.log 5 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp [h2, h3, h4, h5]
