-- Prove2me | solution 1 for WorkbookCorrected.plus_8968
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:55.408011+00:00
-- url     : https://prove2.me/submissions/31af9435-16a1-4a57-a671-08b6528c9fe0

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.choose 3 0 + Nat.choose 4 1 + Nat.choose 5 2 = Nat.choose 6 2 := by
  decide
