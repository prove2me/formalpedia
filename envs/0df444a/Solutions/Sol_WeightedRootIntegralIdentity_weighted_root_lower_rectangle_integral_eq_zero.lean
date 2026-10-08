-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_lower_rectangle_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T15:09:17.933168+00:00
-- url     : https://prove2.me/submissions/9bac2842-7159-49a6-89c4-9af108dbb00c

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_div_differentiableAt_of_im_ne_zero
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (l r ε H : ℝ)
    (hε : 0 < ε) (hεH : ε ≤ H) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x - H * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - ε * Complex.I)) +
        Complex.I • (∫ y : ℝ in -H..-ε, f (r + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in -H..-ε, f (l + y * Complex.I)) = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
  have hf : DifferentiableOn ℂ f ([[l, r]] ×ℂ [[-H, -ε]]) := by
    intro z hz
    have hzmem : z.im ∈ [[-H, -ε]] := (Complex.mem_reProdIm.mp hz).2
    have hzle : z.im ≤ -ε := by
      rcases (Set.mem_uIcc.mp hzmem) with h | h
      · exact h.2
      · exact h.2.trans (neg_le_neg hεH)
    have hzneg : z.im < 0 := lt_of_le_of_lt hzle (neg_neg_of_pos hε)
    exact (WeightedRootIntegralIdentity.weighted_root_div_differentiableAt_of_im_ne_zero
      n a w z (ne_of_lt hzneg)).differentiableWithinAt
  simpa [f, sub_eq_add_neg] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (l - H * Complex.I) (r - ε * Complex.I) (by simpa [sub_eq_add_neg] using hf))
