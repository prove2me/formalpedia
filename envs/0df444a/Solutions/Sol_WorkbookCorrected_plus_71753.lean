-- Prove2me | solution 1 for WorkbookCorrected.plus_71753
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:57.973296+00:00
-- url     : https://prove2.me/submissions/354dfd9f-55f3-491d-a4b4-9a049df9ec4a

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (2 : ℕ) ^ 8 - 2 ^ 5 - 2 ^ 5 + 2 ^ 2 = 196 := by
  norm_num
