-- Prove2me | solution 1 for actuarial_c_loss_expected_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:03:19.491724+00:00
-- url     : https://prove2.me/submissions/8438470f-9848-4ab6-aa9d-dda1af4c164d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_premiumPath
import Definitions.Def_actuarial_c_lossPath
import Definitions.Def_actuarial_c_expectedLoss

open ActuarialAssurances



lemma actH_ppe (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    (∑ k ∈ Finset.range (h+1), p k*premiumPath n v k) = due h n v p := by
  unfold premiumPath due surv
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring

theorem solution (h n : ℕ) (v premium : ℝ) (b p : ℕ → ℝ) : expectedLoss h n v premium b p=term h n v b p-premium*due h n v p := by
  unfold expectedLoss lossPath term
  rw [← actH_ppe, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

