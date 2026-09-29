-- Prove2me | solution 1 for WorkbookCorrected.plus_34349
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:53.735281+00:00
-- url     : https://prove2.me/submissions/76bf4d58-5359-43e4-9e87-4f77b414ad3e

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (650 : ℕ) + 325 - 268 = 707 := by
  norm_num
