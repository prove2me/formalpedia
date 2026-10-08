-- Prove2me | solution 3 for WeightedRootIntegralIdentity.weighted_root_keyhole_contour_boundary_balance
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:33:08.307392+00:00
-- url     : https://prove2.me/submissions/6e7b02a3-c882-418d-8f27-2d90337296fd

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_geometric_mean_cauchy_boundary_integral
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_reciprocal_deriv_at_zero
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_cpow_zero_boundary
open scoped BigOperators Interval
theorem solution (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ) (hpos : ∀ i < n, 0 < a i) (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) (hwpos : ∀ i < n, 0 < w i) (hwsum : (∑ i ∈ Finset.range n, w i) = 1) : 2 * (∫ x in a 0..a (n - 1), (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x) = 2 * Real.pi * (-(deriv (fun u : ℂ => ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re + (∏ i ∈ Finset.range n, (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by
  have hC := WeightedRootIntegralIdentity.weighted_geometric_mean_cauchy_boundary_integral n hn a w hpos hmono hwpos hwsum
  have hD := (WeightedRootIntegralIdentity.weighted_root_reciprocal_deriv_at_zero n a w).deriv
  have hZ := WeightedRootIntegralIdentity.weighted_root_cpow_zero_boundary n a w hpos hwsum
  have hDr : (deriv (fun u : ℂ => ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re = -(∑ i ∈ Finset.range n, w i * a i) := by rw [hD]; simp
  have hZr : (∏ i ∈ Finset.range n, (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re = -(∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by rw [hZ]; norm_cast
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hCscaled := (div_eq_iff hpi).mp hC
  rw [hDr, hZr]
  nlinarith [hCscaled]
