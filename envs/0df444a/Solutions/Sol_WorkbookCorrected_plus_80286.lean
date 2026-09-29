-- Prove2me | solution 1 for WorkbookCorrected.plus_80286
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:25:11.757885+00:00
-- url     : https://prove2.me/submissions/a1cbc6ae-bfd0-46d0-93e6-7d6a49294184

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (1 : ℕ) * 3 ^ 7 - 3 * 2 ^ 7 + 3 * 1 ^ 7 = 1806 := by
  norm_num
