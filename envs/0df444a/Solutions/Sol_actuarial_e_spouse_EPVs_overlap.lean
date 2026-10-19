-- Prove2me | solution 1 for actuarial_e_spouse_EPVs_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:57.569133+00:00
-- url     : https://prove2.me/submissions/4a026252-1aad-49bb-80d5-9f61321dc24e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseEPV
import Definitions.Def_actuarial_e_overlapEPV

open ActuarialDeathE

theorem solution (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) : spouseEPV h n e r g p disc a b c increase false = spouseEPV h n e r g p disc a b c increase true + overlapEPV h n r g p disc c increase := by
  have pt : ∀ i j t, spousePayment h e r g i j t a b c increase false =
      spousePayment h e r g i j t a b c increase true + overlapPayment h r g i j t c increase := by
    intro i j t
    unfold spousePayment overlapPayment
    by_cases ht : t < r + g <;> simp [ht] <;> ring
  unfold spouseEPV overlapEPV ActuarialDeathE.expect ActuarialJointD.expect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  rw [pt, mul_add]

