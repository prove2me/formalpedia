-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootInstantiateNormalizedAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T07:10:46.960961+00:00
-- url     : https://prove2.me/submissions/093a1dff-a4af-4a55-885a-af7561a655fe

import Mathlib
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (J : ℝ)
    (hbalance : 2 * J = 2 * Real.pi *
      ((∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)))) :
    J / Real.pi =
      (∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  nlinarith [hbalance]
