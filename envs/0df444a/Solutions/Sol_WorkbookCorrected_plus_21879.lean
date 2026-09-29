-- Prove2me | solution 1 for WorkbookCorrected.plus_21879
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:11:25.358705+00:00
-- url     : https://prove2.me/submissions/a4dfb276-a9a9-4149-8a53-4ed60440163c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ( (Nat.choose 6 4) + (Nat.choose 5 4) + 11*((Nat.choose 6 3) + (Nat.choose 5 3)) + 30*((Nat.choose 6 2) + (Nat.choose 5 2)) ) = 1100 := by
  decide
