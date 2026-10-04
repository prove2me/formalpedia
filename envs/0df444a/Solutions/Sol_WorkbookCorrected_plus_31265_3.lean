-- Prove2me | solution 3 for WorkbookCorrected.plus_31265
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:23:35.584712+00:00
-- url     : https://prove2.me/submissions/2fea9a72-86e5-43af-b3d8-6be603e1317a

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (81/1000:ℚ) = (81/1000:ℚ) := by
  ring
