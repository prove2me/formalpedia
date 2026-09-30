-- Prove2me | solution 1 for WorkbookCorrected.plus_23470
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-29T20:46:40.488961+00:00
-- url     : https://prove2.me/submissions/3e206838-d0b5-44bc-af41-cf5ed60a0471

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    (9 : ℚ) * (Nat.choose 35 20) =
      (4 : ℚ) * ((Nat.choose 35 20) + (Nat.choose 35 16)) := by
  norm_num [Nat.choose]
