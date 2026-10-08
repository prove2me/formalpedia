-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootGeometricMeanCorollaryV2
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:15:51.258184+00:00
-- url     : https://prove2.me/submissions/7f6df13a-2dc1-49cb-b897-9f55cf5d0093

import Mathlib
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (J : ℝ)
    (hidentity : J / Real.pi =
      (∑ i ∈ Finset.range n, w i * a i) -
        (∏ i ∈ Finset.range n, Real.rpow (a i) (w i))) :
    (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) =
      (∑ i ∈ Finset.range n, w i * a i) - J / Real.pi := by
  linarith
