-- Prove2me | solution 3 for WeightedRootIntegralIdentity.weighted_geometric_mean_cauchy_boundary_integral
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T14:11:47.296658+00:00
-- url     : https://prove2.me/submissions/50f90a66-11bc-42ec-aacb-8a2a2e2bf845

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_keyhole_contour_identity
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_cpow_zero_boundary
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_reciprocal_deriv_at_zero
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))).im / x) / Real.pi
      = (∑ i ∈ Finset.range n, w i * a i)
          - (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by
  have hcontour :=
    WeightedRootIntegralIdentity.weighted_root_keyhole_contour_identity
      n hn a w hpos hmono hwpos hwsum
  have hinfinity :=
    WeightedRootIntegralIdentity.weighted_root_reciprocal_deriv_at_zero n a w
  have hzero :=
    WeightedRootIntegralIdentity.weighted_root_cpow_zero_boundary
      n a w hpos hwsum
  have hderiv :
      deriv
        (fun u : ℂ =>
          ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0 =
        -((∑ i ∈ Finset.range n, w i * a i : ℝ) : ℂ) :=
    hinfinity.deriv
  rw [hderiv, hzero] at hcontour
  simpa only [Complex.neg_re, Complex.ofReal_re, neg_neg, sub_eq_add_neg] using hcontour
