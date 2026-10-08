-- Prove2me | solution 2 for WeightedRootIntegralIdentity.weighted_root_keyhole_contour_identity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-16T12:20:43.320069+00:00
-- url     : https://prove2.me/submissions/49edef69-e139-4635-92e2-cd7e012ffe6a

import Mathlib
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_keyhole_contour_boundary_balance

open scoped BigOperators Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x) / Real.pi =
      -(deriv
          (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
        (∏ i ∈ Finset.range n,
          (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re := by
  have hB := WeightedRootIntegralIdentity.weighted_root_keyhole_contour_boundary_balance n hn a w hpos hmono hwpos hwsum
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi] at hB ⊢
  nlinarith [hB]
