-- Prove2me | solution 1 for WorkbookCorrected.plus_26502
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:31:50.39264+00:00
-- url     : https://prove2.me/submissions/18bab9fa-ce11-4a20-b67f-bb937af98b01

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((6:ℚ)*1 + 5*15 + 4*65 + 3*175 + 2*369 + 1*671)/1296 = (2275:ℚ)/1296 := by
  norm_num
