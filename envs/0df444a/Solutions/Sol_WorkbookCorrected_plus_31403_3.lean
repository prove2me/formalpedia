-- Prove2me | solution 3 for WorkbookCorrected.plus_31403
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:44:37.929813+00:00
-- url     : https://prove2.me/submissions/723f73e9-9750-40f9-9ea3-e44e3d491fc5

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 32 5) - ((Nat.choose 6 1) * (Nat.choose 22 5)) + ((Nat.choose 6 2) * (Nat.choose 12 5)) = 55252 := by
  decide
