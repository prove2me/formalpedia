-- Prove2me | solution 1 for actuarial_f_bridging_before_start
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:17.363889+00:00
-- url     : https://prove2.me/submissions/c227cc79-0c43-467b-8979-5c533a494b97

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeDue

open ActuarialUnderpinsF

theorem solution (start stop t : ℕ)
    (ht : t < start) : bridgeDue start stop t = 0 := by
  unfold bridgeDue
  rw [if_neg (by omega)]
