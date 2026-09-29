-- Prove2me | solution 1 for WorkbookCorrected.plus_57098
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:30:01.801033+00:00
-- url     : https://prove2.me/submissions/310c7bd6-c5da-42a8-a336-bf6e24c21d2f

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.choose 6 2 = 15 := by
  decide
