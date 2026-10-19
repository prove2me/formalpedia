-- Prove2me | solution 1 for actuarial_c_premium_path_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:04:35.414062+00:00
-- url     : https://prove2.me/submissions/9da51822-d758-42c7-89ec-d0b1444dca05

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_premiumPath

open ActuarialAssurances



lemma actH_ppe (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    (∑ k ∈ Finset.range (h+1), p k*premiumPath n v k) = due h n v p := by
  unfold premiumPath due surv
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring

theorem solution (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) : (∑ k ∈ Finset.range (h+1), p k*premiumPath n v k)=due h n v p := by
  exact actH_ppe h n v p

