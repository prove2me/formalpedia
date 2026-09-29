-- Prove2me | solution 1 for WorkbookCorrected.plus_22288
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:27:04.861802+00:00
-- url     : https://prove2.me/submissions/fc3f8072-acf7-4a58-9c45-bb438bf4d44f

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((5:ℚ)/9)*(3/7)*(1/3) = (5:ℚ)/63 := by
  norm_num
