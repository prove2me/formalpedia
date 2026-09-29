-- Prove2me | solution 2 for WorkbookCorrected.plus_6048
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:55:31.484653+00:00
-- url     : https://prove2.me/submissions/5fcebef0-e4b2-4859-92f4-d974ea5d6713

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 64 2) = 2016 := by
  decide
