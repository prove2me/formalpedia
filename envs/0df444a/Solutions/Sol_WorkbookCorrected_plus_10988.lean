-- Prove2me | solution 1 for WorkbookCorrected.plus_10988
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-29T18:22:46.306863+00:00
-- url     : https://prove2.me/submissions/4a756487-c866-4882-ac4f-a231d497f3ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    ((2 : ℚ) / (6 ^ 5)) * (Nat.factorial 5) = (5 : ℚ) / 162 := by
  norm_num [Nat.factorial]
