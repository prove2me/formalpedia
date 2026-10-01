-- Prove2me | solution 1 for WorkbookCorrected.plus_33723
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T07:23:39.366998+00:00
-- url     : https://prove2.me/submissions/4971c1bc-c1a2-46bb-ba60-958988cbc0bf

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 100 50) = (Nat.factorial 100) / ((Nat.factorial 50) * (Nat.factorial 50)) := by
  decide
