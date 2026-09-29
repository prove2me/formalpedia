-- Prove2me | solution 1 for WorkbookCorrected.plus_76882
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:49.715358+00:00
-- url     : https://prove2.me/submissions/3f09ea2c-d1bf-4f15-b397-74e68c8c4f9b

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (3 : ℕ) * 3 * 1 = 9 := by
  norm_num
