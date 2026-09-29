-- Prove2me | solution 1 for WorkbookCorrected.plus_76111
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:29:23.503306+00:00
-- url     : https://prove2.me/submissions/f08a3ff2-0e39-4122-89ad-ace1480798f8

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (29 : ℕ) * 39 * 38 * 37 + 3 * 40 * 39 * 38 = 1768026 := by
  norm_num
