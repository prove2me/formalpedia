-- Prove2me | solution 1 for WorkbookCorrected.plus_1001
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:58.330248+00:00
-- url     : https://prove2.me/submissions/e46a479c-0c21-4152-b881-0a6225927bd9

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.choose 11 5 - Nat.choose 5 2 * Nat.choose 6 3 = 262 := by
  decide
