-- Prove2me | solution 1 for WorkbookCorrected.plus_41596
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:44.605969+00:00
-- url     : https://prove2.me/submissions/18ee73b2-1aa3-4239-8a47-79a57fb0cb6e

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.choose 13 2 = 78 := by
  decide
