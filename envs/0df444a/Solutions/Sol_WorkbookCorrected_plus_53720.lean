-- Prove2me | solution 1 for WorkbookCorrected.plus_53720
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-29T20:17:07.844778+00:00
-- url     : https://prove2.me/submissions/dab4ebb5-f97d-4332-97b3-266e93b3a9f6

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    (323 : ℚ) * (Nat.choose 15 4) =
      (91 : ℚ) * (Nat.choose 20 4) := by
  norm_num [Nat.choose]
