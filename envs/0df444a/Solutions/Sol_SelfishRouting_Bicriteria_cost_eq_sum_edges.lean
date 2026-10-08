-- Prove2me | solution 1 for SelfishRouting.Bicriteria.cost_eq_sum_edges
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:46:55.961977+00:00
-- url     : https://prove2.me/submissions/064d284e-cc7a-4cef-8684-4ceb8852b8a1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

open SelfishRouting.Bicriteria KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (x : Fin R → ℝ) :
    cost A ℓ x = ∑ j, ℓ j (linkFlow A x j) * linkFlow A x j := by
  classical
  unfold cost pathLatency
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold linkFlow
  simp_rw [Finset.mul_sum, mul_assoc]

#print axioms solution
