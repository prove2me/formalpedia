-- Prove2me | solution 1 for WorkbookCorrected.plus_48406
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-29T20:08:26.418935+00:00
-- url     : https://prove2.me/submissions/d423870f-ab75-4ed5-ac91-cda9d5f0b220

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    (15 : ℚ) * ((Nat.factorial 4) * (Nat.factorial 2)) =
      (1 : ℚ) * (Nat.factorial 6) := by
  norm_num [Nat.factorial]
