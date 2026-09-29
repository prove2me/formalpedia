-- Prove2me | solution 1 for WorkbookCorrected.plus_59236
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:30:00.866688+00:00
-- url     : https://prove2.me/submissions/64d6d9e8-b07c-48a2-ae8c-63b00fc45953

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.choose 4 2 = 6 := by
  decide
