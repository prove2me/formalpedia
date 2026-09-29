-- Prove2me | solution 1 for WorkbookCorrected.plus_40193
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:12:09.318598+00:00
-- url     : https://prove2.me/submissions/030d3417-2d5d-42d1-a638-90dd24302950

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 3 2 * Nat.factorial 4) = 72 := by
  decide
