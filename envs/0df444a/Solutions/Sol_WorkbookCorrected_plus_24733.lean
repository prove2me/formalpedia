-- Prove2me | solution 1 for WorkbookCorrected.plus_24733
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:53:00.345517+00:00
-- url     : https://prove2.me/submissions/085dbbc6-52da-43f9-b91a-5c3a87cccfae

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 11 6) - 1 - 30 - 6 = 425 := by
  decide
