-- Prove2me | solution 1 for WorkbookCorrected.plus_44263
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:11:50.903839+00:00
-- url     : https://prove2.me/submissions/bb9be722-e662-4a3c-af72-52597a513260

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 6 5 + (Nat.choose 5 5) + 11 * (Nat.choose 6 4 + (Nat.choose 5 4)) + 30 * (Nat.choose 6 3 + (Nat.choose 5 3))) = 1127 := by
  decide
