-- Prove2me | solution 1 for WorkbookCorrected.plus_20865
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:52:57.759034+00:00
-- url     : https://prove2.me/submissions/c87bd1a3-2951-4cf0-a8a6-84ad862e9fb2

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 7 3) = 35 := by
  decide
