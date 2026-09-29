-- Prove2me | solution 1 for WorkbookCorrected.plus_5842
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:23:11.632515+00:00
-- url     : https://prove2.me/submissions/4a32b3a8-9435-40b3-ab66-2d95dc9ea9a1

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 16 2 * (Nat.choose 14 2) * (Nat.choose 12 2) * (Nat.choose 10 2) * (Nat.choose 8 2) * (Nat.choose 6 2) * (Nat.choose 4 2) * (Nat.choose 2 2)) = 81729648000 := by
  decide
