-- Prove2me | solution 1 for WorkbookCorrected.plus_66909
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:23:30.600479+00:00
-- url     : https://prove2.me/submissions/7ca4a4e5-8674-4ee8-af26-0be76d0219b7

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 25 3) = 2300 := by
  decide
