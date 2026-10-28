-- Prove2me | solution 1 for actuarial_f_bridging_inside
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:25.272716+00:00
-- url     : https://prove2.me/submissions/d0b143e9-2b5d-4182-a368-86a48bacba8e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeDue

open ActuarialUnderpinsF

theorem solution (start stop t : ℕ)
    (hs : start ≤ t) (ht : t < stop) :
    bridgeDue start stop t = 1 := by
  unfold bridgeDue
  rw [if_pos ⟨hs, ht⟩]
