-- Prove2me | solution 1 for actuarial_e_spouse_ineligible_before_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:21:15.122989+00:00
-- url     : https://prove2.me/submissions/b60ce07a-a20a-4473-a7bf-685570793a1c

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

theorem solution (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (ht : t ≤ i + 1) : spousePayment h e r g i j t a b c increase false = 0 := by
  unfold spousePayment spouseDue
  rw [if_neg (by omega)]; ring
