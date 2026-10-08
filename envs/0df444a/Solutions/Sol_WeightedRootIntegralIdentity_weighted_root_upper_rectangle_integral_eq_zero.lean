-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_upper_rectangle_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T15:04:00.366368+00:00
-- url     : https://prove2.me/submissions/3045299a-56e2-475f-ab70-e2f38c31e37f

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_div_differentiableAt_of_im_ne_zero
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (l r ε H : ℝ)
    (hε : 0 < ε) (hεH : ε ≤ H) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
        (∫ x : ℝ in l..r, f (x + H * Complex.I)) +
        Complex.I • (∫ y : ℝ in ε..H, f (r + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in ε..H, f (l + y * Complex.I)) = 0 := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
  have hf : DifferentiableOn ℂ f ([[l, r]] ×ℂ [[ε, H]]) := by
    intro z hz
    have hzmem : z.im ∈ [[ε, H]] := (Complex.mem_reProdIm.mp hz).2
    have hεz : ε ≤ z.im := by
      rcases (Set.mem_uIcc.mp hzmem) with h | h
      · exact h.1
      · exact hεH.trans h.1
    have hzpos : 0 < z.im := lt_of_lt_of_le hε hεz
    exact (WeightedRootIntegralIdentity.weighted_root_div_differentiableAt_of_im_ne_zero
      n a w z (ne_of_gt hzpos)).differentiableWithinAt
  simpa [f] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (l + ε * Complex.I) (r + H * Complex.I) (by simpa using hf))
