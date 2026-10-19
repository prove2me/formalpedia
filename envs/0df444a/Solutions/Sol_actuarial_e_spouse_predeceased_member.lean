-- Prove2me | solution 1 for actuarial_e_spouse_predeceased_member
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:21:22.861061+00:00
-- url     : https://prove2.me/submissions/65918826-afe3-443a-990e-70acac1fed08

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

theorem solution (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (hj : j ≤ i) : spousePayment h e r g i j t a b c increase false = 0 := by
  unfold spousePayment spouseDue
  rw [if_neg (by omega)]; ring
