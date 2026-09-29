-- Prove2me | solution 1 for WorkbookCorrected.plus_67507
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:28.358911+00:00
-- url     : https://prove2.me/submissions/16f8abef-4919-49e4-bb4a-87faa66081ec

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (13 : ℕ) * 12 + (13 * 12) / 2 = 234 := by
  norm_num
