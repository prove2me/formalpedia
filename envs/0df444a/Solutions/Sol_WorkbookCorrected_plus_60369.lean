-- Prove2me | solution 1 for WorkbookCorrected.plus_60369
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:29:22.398786+00:00
-- url     : https://prove2.me/submissions/b084cb9a-0db8-4772-8f5d-c18945c43834

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (1792 : ℕ) - 400 - 432 - 464 = 496 := by
  norm_num
