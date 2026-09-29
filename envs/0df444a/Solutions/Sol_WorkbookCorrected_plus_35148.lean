-- Prove2me | solution 1 for WorkbookCorrected.plus_35148
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:53:03.972632+00:00
-- url     : https://prove2.me/submissions/fd84fef8-d1d5-4073-b991-abda46ed3502

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 10 4) - ((Nat.choose 6 4) + (Nat.choose 4 1) * (Nat.choose 6 3)) = 115 := by
  decide
