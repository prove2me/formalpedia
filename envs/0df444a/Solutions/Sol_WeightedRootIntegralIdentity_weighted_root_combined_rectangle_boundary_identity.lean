-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_combined_rectangle_boundary_identity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T15:14:22.485049+00:00
-- url     : https://prove2.me/submissions/51d18c92-10a0-46a4-8234-a9888e85044e

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_upper_rectangle_integral_eq_zero
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_lower_rectangle_integral_eq_zero
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (l r ε H : ℝ)
    (hε : 0 < ε) (hεH : ε ≤ H) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
      (∫ x : ℝ in l..r, f (x + H * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - H * Complex.I)) -
        Complex.I • (∫ y : ℝ in ε..H, f (r + y * Complex.I)) +
        Complex.I • (∫ y : ℝ in ε..H, f (l + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in -H..-ε, f (r + y * Complex.I)) +
        Complex.I • (∫ y : ℝ in -H..-ε, f (l + y * Complex.I)) := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
  have hup := WeightedRootIntegralIdentity.weighted_root_upper_rectangle_integral_eq_zero
    n a w l r ε H hε hεH
  have hlow := WeightedRootIntegralIdentity.weighted_root_lower_rectangle_integral_eq_zero
    n a w l r ε H hε hεH
  dsimp only at hup hlow
  linear_combination hup + hlow
