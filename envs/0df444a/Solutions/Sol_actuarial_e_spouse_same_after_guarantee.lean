-- Prove2me | solution 1 for actuarial_e_spouse_same_after_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:21:30.6476+00:00
-- url     : https://prove2.me/submissions/a86ccc7c-bb17-436e-b2de-c493bd9d2ebd

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

theorem solution (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (ht : r + g ≤ t) : spousePayment h e r g i j t a b c increase false = spousePayment h e r g i j t a b c increase true := by
  unfold spousePayment
  have : ¬ t < r + g := by omega
  simp [this]
