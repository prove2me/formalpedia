-- Prove2me | solution 1 for WorkbookCorrected.plus_61333
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:37.473777+00:00
-- url     : https://prove2.me/submissions/1d7ed65e-2c40-47db-bc66-3beeb9cd97f6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

theorem solution : (27 : ℝ) / 216 = 1 / 8 := by
  norm_num
