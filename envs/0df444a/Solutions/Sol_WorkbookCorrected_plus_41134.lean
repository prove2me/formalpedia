-- Prove2me | solution 1 for WorkbookCorrected.plus_41134
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:52:59.176724+00:00
-- url     : https://prove2.me/submissions/b4c82bd3-aefa-4609-bd1b-54c981d1d672

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 11 5) - (Nat.choose 5 3) = 452 := by
  decide
