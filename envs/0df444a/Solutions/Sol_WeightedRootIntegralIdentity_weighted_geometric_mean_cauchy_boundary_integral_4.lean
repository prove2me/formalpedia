-- Prove2me | solution 4 for WeightedRootIntegralIdentity.weighted_geometric_mean_cauchy_boundary_integral
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:37:23.703811+00:00
-- url     : https://prove2.me/submissions/8710a392-c5b0-4d12-a78e-c31adfcc8b47

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_keyhole_contour_identity
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_reciprocal_deriv_at_zero
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_cpow_zero_boundary

open scoped BigOperators Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))).im / x) / Real.pi
      = (∑ i ∈ Finset.range n, w i * a i)
          - (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
  have hK := WeightedRootIntegralIdentity.weighted_root_keyhole_contour_identity n hn a w hpos hmono hwpos hwsum
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
  rw [hDr, hZr] at hK
  convert hK using 1 <;> ring
