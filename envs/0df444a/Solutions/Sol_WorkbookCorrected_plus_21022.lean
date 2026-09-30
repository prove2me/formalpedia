-- Prove2me | solution 1 for WorkbookCorrected.plus_21022
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:04:25.296733+00:00
-- url     : https://prove2.me/submissions/82dd38ca-4851-43e0-b55a-95c466e95b90

import Mathlib.Tactic.NormNum

theorem solution : 1 + 4 + 9 + 16 + 25 + 36 + 49 + 64 + 81 + 100 = 10 * 21 * 11 / 6 := by
  decide
