-- Prove2me | solution 1 for WorkbookCorrected.plus_67501
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:29.498174+00:00
-- url     : https://prove2.me/submissions/aebf2950-cfea-4083-b324-0ebaf745b335

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((3 : ℕ) + 3) ^ 3 = 3 ^ 3 * 3 ^ 0 + 3 * (3 ^ 2 * 3 ^ 1) + 3 * (3 ^ 1 * 3 ^ 2) + 3 ^ 0 * 3 ^ 3 := by
  norm_num
