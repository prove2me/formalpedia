-- Prove2me | solution 1 for actuarial_f_guarantee_no_estate_after_expiry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:07.492843+00:00
-- url     : https://prove2.me/submissions/ec87269b-3fd4-4eae-869c-37e7e62b2c5e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateInstalment

open ActuarialUnderpinsF

theorem solution (h r g z i t : ℕ)
    (estateBase ge : ℕ → ℝ) (ht : r+g ≤ t) :
    estateInstalment h r g z i t estateBase ge = 0 := by
  unfold estateInstalment estateDue
  rw [if_neg (by omega), mul_zero]
