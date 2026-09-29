-- Prove2me | solution 1 for WorkbookCorrected.plus_4695
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:56.838017+00:00
-- url     : https://prove2.me/submissions/cfc2809f-ce7d-41d2-af5b-c76498c01db3

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (8 : ℕ) ^ 2 * 9 ^ 2 = 5184 := by
  norm_num
