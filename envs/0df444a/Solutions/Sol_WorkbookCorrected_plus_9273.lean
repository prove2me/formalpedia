-- Prove2me | solution 1 for WorkbookCorrected.plus_9273
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T20:56:15.028593+00:00
-- url     : https://prove2.me/submissions/cf93acea-3417-4073-bcf1-8a6ac08d6d27

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.choose 8 4) * (Nat.factorial 7) * (Nat.factorial 4)) = 8467200 := by
  decide
