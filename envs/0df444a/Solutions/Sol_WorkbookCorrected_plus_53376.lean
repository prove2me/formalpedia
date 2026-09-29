-- Prove2me | solution 1 for WorkbookCorrected.plus_53376
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:30:02.744722+00:00
-- url     : https://prove2.me/submissions/bc752ccc-2a3e-4792-b729-2e09a8287462

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (14 : ℕ) * Nat.factorial 3 * Nat.factorial 3 + 4 * Nat.factorial 3 * Nat.factorial 3 = 18 * Nat.factorial 3 * Nat.factorial 3 := by
  decide
