-- Prove2me | solution 1 for WorkbookCorrected.plus_21622
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:23:41.257983+00:00
-- url     : https://prove2.me/submissions/916148b9-40b6-4f4d-b3c3-b77aeeb7dafc

import Mathlib.Tactic.NormNum

theorem solution : (10 = 5 + 5) ∧ (11 = 5 + 6) ∧ (12 = 6 + 6) ∧ (13 = 5 + 6 + 2) ∧ (14 = 5 + 5 + 2 + 2) := by
  decide
