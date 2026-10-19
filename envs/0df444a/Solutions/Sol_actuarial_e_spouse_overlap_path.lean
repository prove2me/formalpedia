-- Prove2me | solution 1 for actuarial_e_spouse_overlap_path
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:19:43.002404+00:00
-- url     : https://prove2.me/submissions/131cdbae-066f-4a65-a8c8-94c3977f95af

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spousePayment
import Definitions.Def_actuarial_e_overlapPayment

open ActuarialDeathE

theorem solution (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) : spousePayment h e r g i j t a b c increase false = spousePayment h e r g i j t a b c increase true + overlapPayment h r g i j t c increase := by
  unfold spousePayment overlapPayment
  by_cases ht : t < r + g <;> simp [ht] <;> ring

