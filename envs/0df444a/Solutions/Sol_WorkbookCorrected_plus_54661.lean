-- Prove2me | solution 1 for WorkbookCorrected.plus_54661
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:23:18.292883+00:00
-- url     : https://prove2.me/submissions/feafb3f4-bdf1-44dc-8cb5-055f17d9a1e7

import Mathlib.Tactic.NormNum

theorem solution : (123 + 4 + 5 + 6 + 7 + 8 - 9 = 144) ∧ (123 - 4 - 5 + 6 + 7 + 8 + 9 = 144) := by
  decide
