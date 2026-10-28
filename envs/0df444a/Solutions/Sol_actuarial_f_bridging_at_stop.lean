-- Prove2me | solution 1 for actuarial_f_bridging_at_stop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:20.964408+00:00
-- url     : https://prove2.me/submissions/72ec87e9-a86f-4cc7-b25d-95c5cd189a6a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeDue

open ActuarialUnderpinsF

theorem solution (start stop : ℕ) :
    bridgeDue start stop stop = 0 := by
  unfold bridgeDue
  rw [if_neg (by omega)]
