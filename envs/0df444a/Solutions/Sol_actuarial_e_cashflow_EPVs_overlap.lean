-- Prove2me | solution 1 for actuarial_e_cashflow_EPVs_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:04:57.276011+00:00
-- url     : https://prove2.me/submissions/14d61b42-79fe-491a-aca0-1c4c43682d12

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_overlapEPV
import Definitions.Def_actuarial_e_cashflowEPV

open ActuarialDeathE

theorem solution (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) : cashflowEPV h n e r g p disc service defer retire base a b c increase false = cashflowEPV h n e r g p disc service defer retire base a b c increase true + overlapEPV h n r g p disc c increase := by
  have pt : ∀ i j t, spousePayment h e r g i j t a b c increase false =
      spousePayment h e r g i j t a b c increase true + overlapPayment h r g i j t c increase := by
    intro i j t
    unfold spousePayment overlapPayment
    by_cases ht : t < r + g <;> simp [ht] <;> ring
  have key : spouseEPV h n e r g p disc a b c increase false =
      spouseEPV h n e r g p disc a b c increase true + overlapEPV h n r g p disc c increase := by
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
  unfold cashflowEPV
  rw [key]; ring
