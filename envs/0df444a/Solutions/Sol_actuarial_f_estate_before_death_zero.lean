-- Prove2me | solution 1 for actuarial_f_estate_before_death_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:33:27.153578+00:00
-- url     : https://prove2.me/submissions/5a31d612-0e98-4124-9140-bd11608ca40d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem solution (h r g i t : ℕ) (ht : t ≤ i) :
    estateDue h r g i t = 0 := by
  unfold estateDue
  rw [if_neg (by omega)]
