-- Prove2me | solution 1 for actuarial_e_spouse_suppressed_within_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:21:38.184691+00:00
-- url     : https://prove2.me/submissions/706d09a9-11ba-4be8-8d8a-75f32d4b4f46

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spousePayment

open ActuarialDeathE

theorem solution (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (her : e ≤ r) (hi : r ≤ i) (ht : t < r + g) : spousePayment h e r g i j t a b c increase true = 0 := by
  unfold spousePayment active deferred
  rw [if_neg (by omega), if_neg (by omega)]
  simp [ht]
