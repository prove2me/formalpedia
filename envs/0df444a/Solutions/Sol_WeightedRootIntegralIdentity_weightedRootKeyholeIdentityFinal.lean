-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootKeyholeIdentityFinal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T09:01:18.656552+00:00
-- url     : https://prove2.me/submissions/1f2399a2-edeb-46c7-bb44-78df62ebeb95

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootInstantiateNormalizedAlgebra

open WeightedRootIntegralIdentity

theorem solution (n : ℕ) (a w : ℕ → ℝ) (J : ℝ)
    (hbalance : 2 * J = 2 * Real.pi *
      ((∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)))) :
    J / Real.pi =
      (∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) :=
  WeightedRootIntegralIdentity.weightedRootInstantiateNormalizedAlgebra n a w J hbalance
