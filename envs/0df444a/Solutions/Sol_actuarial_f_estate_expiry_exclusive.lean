-- Prove2me | solution 1 for actuarial_f_estate_expiry_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:33:22.467995+00:00
-- url     : https://prove2.me/submissions/430aba0d-cb00-4407-91b5-6c4e635b61eb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem solution (h r g i : ℕ) :
    estateDue h r g i (r + g) = 0 := by
  unfold estateDue
  rw [if_neg (by omega)]
