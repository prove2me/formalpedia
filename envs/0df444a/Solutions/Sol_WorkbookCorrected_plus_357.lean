-- Prove2me | solution 1 for WorkbookCorrected.plus_357
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:53:01.488642+00:00
-- url     : https://prove2.me/submissions/9f116db8-0c22-42b6-ac40-80cb8fbed74e

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 14 5) - (Nat.choose 10 5) = 1750 := by
  decide
