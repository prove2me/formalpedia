-- Prove2me | solution 1 for WorkbookCorrected.plus_33342
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:52:55.450111+00:00
-- url     : https://prove2.me/submissions/87a84fe6-b639-4a03-8aac-8fbf5282bb8d

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 12 3) / 2 = 110 := by
  decide
