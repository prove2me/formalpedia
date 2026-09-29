-- Prove2me | solution 1 for WorkbookCorrected.plus_78077
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:59.347453+00:00
-- url     : https://prove2.me/submissions/210e4efc-1442-4b99-b545-8a809c8bf314

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (6 : ℕ) * 1 + 10 * 1 + 15 * 1 + 7 * 3 = 52 := by
  norm_num
