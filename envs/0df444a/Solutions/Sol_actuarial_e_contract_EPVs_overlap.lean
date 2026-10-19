-- Prove2me | solution 1 for actuarial_e_contract_EPVs_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:05:27.326034+00:00
-- url     : https://prove2.me/submissions/c189f272-6d09-4f19-8cd2-10952a4b3aa5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_contractEPV
import Definitions.Def_actuarial_e_overlapEPV

open ActuarialDeathE

theorem solution (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) : contractEPV h n e r g p disc service defer retire base a b c increase false = contractEPV h n e r g p disc service defer retire base a b c increase true + overlapEPV h n r g p disc c increase := by
  have pt : ∀ i j t, spousePayment h e r g i j t a b c increase false =
      spousePayment h e r g i j t a b c increase true + overlapPayment h r g i j t c increase := by
    intro i j t
    unfold spousePayment overlapPayment
    by_cases ht : t < r + g <;> simp [ht] <;> ring
  have pr : ∀ i j, realisedPV h n e r g i j disc service defer retire base a b c increase false =
      realisedPV h n e r g i j disc service defer retire base a b c increase true +
        ∑ t ∈ Finset.range n, disc t * overlapPayment h r g i j t c increase := by
    intro i j
    unfold realisedPV instalment
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pt]; ring
  unfold contractEPV overlapEPV ActuarialDeathE.expect ActuarialJointD.expect
  simp only [pr, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring
