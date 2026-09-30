-- Prove2me | solution 1 for WorkbookCorrected.plus_4183
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:58:38.450881+00:00
-- url     : https://prove2.me/submissions/65ea5d9c-7d14-4bd7-b548-768dee6d63db

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem solution : Real.log 2 / Real.log 6 + Real.log 3 / Real.log 6 = 1 := by
  have h6 : Real.log 6 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp [h6]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have : Real.log 2 + Real.log 3 = Real.log 6 := by
    have h := (Real.log_mul h2 h3).symm
    convert h using 2
    norm_num
  linarith
