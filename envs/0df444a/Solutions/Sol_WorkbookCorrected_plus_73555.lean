-- Prove2me | solution 1 for WorkbookCorrected.plus_73555
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:54.413102+00:00
-- url     : https://prove2.me/submissions/3f1185ee-b3fc-4325-8983-3b2a7c1f24cb

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (20 : ℕ) + 360 + 1080 + 400 = 1860 := by
  norm_num
