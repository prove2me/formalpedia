-- Prove2me | solution 1 for WorkbookCorrected.plus_14183
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T06:46:55.053006+00:00
-- url     : https://prove2.me/submissions/b3098507-bedc-4bf6-a3a4-947f30e75a70

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem solution : (3999999/2000:ℚ) = (3999999/2000:ℚ) := by
  norm_num
