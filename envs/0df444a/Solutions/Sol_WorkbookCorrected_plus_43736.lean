-- Prove2me | solution 1 for WorkbookCorrected.plus_43736
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T20:56:15.001827+00:00
-- url     : https://prove2.me/submissions/1d31832f-6ea4-4588-8a50-8bc03f27f400

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 12 5)) = 792 := by
  decide
