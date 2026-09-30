-- Prove2me | solution 1 for WorkbookCorrected.plus_40877
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:41:40.650469+00:00
-- url     : https://prove2.me/submissions/09fe9c6d-7966-49fb-b621-d76bf276b498

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (0:ℚ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = (0:ℚ) := by
  norm_num
