-- Prove2me | solution 1 for WorkbookCorrected.plus_22293
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:27:28.158311+00:00
-- url     : https://prove2.me/submissions/83de8878-4d74-45ce-aa28-fc42f80fe4ae

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((2:ℚ)/3) ^ 2 * (1/3) ^ 2 * 3 = (4:ℚ)/27 := by
  norm_num
