-- Prove2me | solution 1 for WorkbookCorrected.plus_50436
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:12:27.267978+00:00
-- url     : https://prove2.me/submissions/af03da32-f18b-40c1-a961-a5769cb951b1

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 8 2) * 16) = 448 := by
  decide
