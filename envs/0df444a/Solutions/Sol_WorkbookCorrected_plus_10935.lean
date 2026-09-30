-- Prove2me | solution 1 for WorkbookCorrected.plus_10935
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-29T20:46:40.345602+00:00
-- url     : https://prove2.me/submissions/b5e0a772-c8eb-46e1-bb57-990820786ad8

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    ((2 : ℚ) * (Nat.choose 12 2) + 6 * (Nat.choose 6 2)) /
      (Nat.choose 60 2) = (37 : ℚ) / 295 := by
  norm_num [Nat.choose]
