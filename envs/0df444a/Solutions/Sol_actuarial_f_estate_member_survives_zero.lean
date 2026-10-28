-- Prove2me | solution 1 for actuarial_f_estate_member_survives_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:01.790104+00:00
-- url     : https://prove2.me/submissions/b1d1d17b-35ce-4c2c-9e59-61f8d6af2e49

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem solution (h r g t : ℕ) :
    estateDue h r g h t = 0 := by
  unfold estateDue
  rw [if_neg (by omega)]
