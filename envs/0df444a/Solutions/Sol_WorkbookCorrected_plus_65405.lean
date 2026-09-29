-- Prove2me | solution 1 for WorkbookCorrected.plus_65405
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:25:13.108917+00:00
-- url     : https://prove2.me/submissions/573b5d7e-2818-479d-9215-d5b62107e86c

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (8 : ℕ) ^ 2 * 10 ^ 8 = 6400000000 := by
  norm_num
