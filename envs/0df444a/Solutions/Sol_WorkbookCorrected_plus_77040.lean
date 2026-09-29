-- Prove2me | solution 1 for WorkbookCorrected.plus_77040
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:51.115782+00:00
-- url     : https://prove2.me/submissions/30867fa0-8470-439b-9c1d-26e72d561a84

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (750 : ℕ) - 536 = 214 := by
  norm_num
