-- Prove2me | solution 1 for WorkbookCorrected.plus_59225
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:53:02.810401+00:00
-- url     : https://prove2.me/submissions/fc77149f-03b4-48d2-98e5-6d8148cb773f

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 9 3) * (Nat.choose 6 3) * (Nat.choose 3 3)) = 1680 := by
  decide
