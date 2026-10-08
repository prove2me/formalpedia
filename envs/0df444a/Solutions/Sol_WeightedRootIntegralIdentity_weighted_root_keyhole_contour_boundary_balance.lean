-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_keyhole_contour_boundary_balance
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T12:09:10.246887+00:00
-- url     : https://prove2.me/submissions/bcdca461-aa92-4dbf-964f-3b6e32b8bad4

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_geometric_mean_cauchy_boundary_integral
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_reciprocal_deriv_at_zero
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_cpow_zero_boundary

open scoped BigOperators Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    2 * (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x) =
      2 * Real.pi *
        (-(deriv
          (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
          (∏ i ∈ Finset.range n,
            (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re) := by
  have hC := WeightedRootIntegralIdentity.weighted_geometric_mean_cauchy_boundary_integral n hn a w hpos hmono hwpos hwsum
  have hD := (WeightedRootIntegralIdentity.weighted_root_reciprocal_deriv_at_zero n a w).deriv
  have hZ := WeightedRootIntegralIdentity.weighted_root_cpow_zero_boundary n a w hpos hwsum
  have hDr : (deriv
      (fun u : ℂ =>
        ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re =
      -(∑ i ∈ Finset.range n, w i * a i) := by
    rw [hD]
    simp
  have hZr : (∏ i ∈ Finset.range n,
        (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re =
      -(∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
    rw [hZ]
    have hprod_re : ∀ m : ℕ,
        (∏ i ∈ Finset.range m, ((a i ^ w i : ℝ) : ℂ)).re =
          ∏ i ∈ Finset.range m, a i ^ w i := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          simp only [Finset.prod_range_succ]
          simp [Complex.mul_re, ih]
    simpa [hprod_re n]
  rw [hDr, hZr]
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi] at hC
  simp at hC ⊢
  norm_num at hC ⊢
  nlinarith [hC]
