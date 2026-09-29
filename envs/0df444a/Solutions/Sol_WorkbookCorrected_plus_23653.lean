-- Prove2me | solution 1 for WorkbookCorrected.plus_23653
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:47.681784+00:00
-- url     : https://prove2.me/submissions/3739317c-6f61-4ece-9dfc-9428c49e1d8e

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (5 : ℕ) ^ 5 = 3125 := by
  norm_num
