-- Prove2me | solution 1 for WorkbookCorrected.plus_45360
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:28:57.186516+00:00
-- url     : https://prove2.me/submissions/6a73225f-073c-4c73-8a4f-ddca1ca542a4

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((1:ℚ)/2)*(2/3) = (1:ℚ)/3 := by
  norm_num
