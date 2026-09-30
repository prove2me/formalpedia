-- Prove2me | solution 1 for WorkbookCorrected.plus_48990
-- status  : ACCEPTED   (disprove)
-- author  : @Sneed
-- created : 2026-09-29T20:31:52.637037+00:00
-- url     : https://prove2.me/submissions/6d2d56e2-687d-43dd-a337-e4817818f56b

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    ¬ ((Nat.choose (16 + 3) 3) - (Nat.choose (11 + 3) 3) -
      (Nat.choose (10 + 3) 3) - 2 * (Nat.choose (9 + 3) 3) +
      (Nat.choose (5 + 3) 3) + 2 * (Nat.choose (4 + 3) 3) +
      2 * (Nat.choose (3 + 3) 3) + (Nat.choose (2 + 3) 3) = 55) := by
  norm_num [Nat.choose]
