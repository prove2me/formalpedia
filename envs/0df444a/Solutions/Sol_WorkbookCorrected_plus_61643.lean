-- Prove2me | solution 1 for WorkbookCorrected.plus_61643
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:29:21.163281+00:00
-- url     : https://prove2.me/submissions/cf045474-8d71-4117-b5c5-d6139380826e

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (52 : ℕ) * 5 + 4 * 73 + 8 * 26 = 760 := by
  norm_num
