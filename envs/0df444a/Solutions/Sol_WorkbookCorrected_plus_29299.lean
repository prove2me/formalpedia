-- Prove2me | solution 1 for WorkbookCorrected.plus_29299
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T07:04:03.779886+00:00
-- url     : https://prove2.me/submissions/2ac890f2-970f-4d20-a5e1-7f87ac174504

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 8) + (Nat.factorial 9) + (Nat.factorial 10) = 4032000 := by
  decide
