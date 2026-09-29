-- Prove2me | solution 1 for WorkbookCorrected.plus_51564
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:33.03273+00:00
-- url     : https://prove2.me/submissions/3a03a711-ee8d-48e3-8d4f-9dcfc2ae7f9c

import Mathlib.Data.Nat.Choose.Basic

theorem solution (n : ℕ) : Nat.choose n 0 = 1 := by
  exact Nat.choose_zero_right n
