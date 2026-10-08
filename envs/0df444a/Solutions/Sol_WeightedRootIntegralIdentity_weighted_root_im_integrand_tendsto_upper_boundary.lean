-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_im_integrand_tendsto_upper_boundary
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T07:59:49.666126+00:00
-- url     : https://prove2.me/submissions/f454ed06-781d-4584-aff1-15db9d02153e

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_integrand_tendsto_upper_boundary
open Filter Set Topology
open scoped BigOperators

theorem solution (n : ℕ) (a w : ℕ → ℝ) (x : ℝ)
    (hx : x ≠ 0) (hxa : ∀ i < n, x ≠ a i) :
    Tendsto
      (fun ε : ℝ =>
        ((∏ i ∈ Finset.range n,
          (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) + ε * Complex.I)).im)
      (𝓝[>] 0)
      (𝓝 (((∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)) / (x : ℂ)).im)) := by
  exact Complex.continuous_im.continuousAt.tendsto.comp
    (WeightedRootIntegralIdentity.weighted_root_integrand_tendsto_upper_boundary
      n a w x hx hxa)
