-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootFinalWeightedRootIdentity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T09:38:53.519326+00:00
-- url     : https://prove2.me/submissions/5c1d1299-6174-460f-a87a-d5bb40345ac6

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootInstantiateNormalizedAlgebra
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (J : ℝ)
    (hbalance : 2 * J = 2 * Real.pi *
      ((∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)))) :
    J / Real.pi =
      (∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
  exact WeightedRootIntegralIdentity.weightedRootInstantiateNormalizedAlgebra n a w J hbalance
