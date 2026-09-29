-- Prove2me | solution 1 for WorkbookCorrected.plus_31403
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:43:24.183545+00:00
-- url     : https://prove2.me/submissions/51a7dcd8-ae8d-4974-96af-79d855f3ce04

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 32 5) - ((Nat.choose 6 1) * (Nat.choose 22 5)) + ((Nat.choose 6 2) * (Nat.choose 12 5)) = 55252 := by
  decide
