-- Prove2me | solution 1 for actuarial_e_instalment_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:17:23.794658+00:00
-- url     : https://prove2.me/submissions/01e81590-be8d-45a9-b4cb-4316779fa3e0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_overlapPayment
import Definitions.Def_actuarial_e_instalment

open ActuarialDeathE

theorem solution (h e r g i j t : ℕ) (base a b c increase : ℕ → ℝ) : instalment h e r g i j t base a b c increase false = instalment h e r g i j t base a b c increase true + overlapPayment h r g i j t c increase := by
  have pt : ∀ i j t, spousePayment h e r g i j t a b c increase false =
      spousePayment h e r g i j t a b c increase true + overlapPayment h r g i j t c increase := by
    intro i j t
    unfold spousePayment overlapPayment
    by_cases ht : t < r + g <;> simp [ht] <;> ring
  unfold instalment
  rw [pt]; ring
