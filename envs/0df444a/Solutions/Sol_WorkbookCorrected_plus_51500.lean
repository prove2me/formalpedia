-- Prove2me | solution 1 for WorkbookCorrected.plus_51500
-- status  : ACCEPTED   (disprove)
-- author  : @Sneed
-- created : 2026-09-30T09:58:13.930463+00:00
-- url     : https://prove2.me/submissions/a31a6c4c-f8fa-4d57-ba0d-11b5ba956fd2

import Mathlib.Tactic.NormNum

theorem solution : ¬ (4 + 4 + 2 = 8) := by
  norm_num
