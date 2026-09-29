-- Prove2me | solution 1 for WorkbookCorrected.plus_6006
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:58:04.097825+00:00
-- url     : https://prove2.me/submissions/637d11cb-cd23-4e3b-afae-4747de78906d

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 9 2) * 11 = (Nat.choose 12 2) * 6 := by
  decide
