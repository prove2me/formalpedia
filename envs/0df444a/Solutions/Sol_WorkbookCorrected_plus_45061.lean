-- Prove2me | solution 1 for WorkbookCorrected.plus_45061
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:52:54.267163+00:00
-- url     : https://prove2.me/submissions/babbff49-50a7-449e-b57a-234040626dbf

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 5 3) - 1 = 9 := by
  decide
