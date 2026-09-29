-- Prove2me | solution 1 for WorkbookCorrected.plus_79743
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:52.345483+00:00
-- url     : https://prove2.me/submissions/7fe01645-ecb4-4f4b-9149-56b2a74fa007

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (6 : ℕ) ^ 10 = 2 ^ 10 * 3 ^ 10 := by
  norm_num
