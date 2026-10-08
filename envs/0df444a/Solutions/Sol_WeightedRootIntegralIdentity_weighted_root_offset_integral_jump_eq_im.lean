-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_offset_integral_jump_eq_im
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T20:43:46.852967+00:00
-- url     : https://prove2.me/submissions/674461d2-4e1c-4c25-be96-dad4a4f7488d

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_upper_lower_conj
open scoped BigOperators Interval ComplexConjugate

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (l r ε : ℝ) (hε : 0 < ε) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
      2 * Complex.I *
        ((((∫ x : ℝ in l..r, f (x + ε * Complex.I))).im : ℝ) : ℂ) := by
  dsimp only
  let f : ℂ → ℂ := fun z =>
    (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
  change (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
      (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
    2 * Complex.I *
      ((((∫ x : ℝ in l..r, f (x + ε * Complex.I))).im : ℝ) : ℂ)
  have hpoint : ∀ x : ℝ, f (x - ε * Complex.I) =
      starRingEnd ℂ (f (x + ε * Complex.I)) := by
    intro x
    exact WeightedRootIntegralIdentity.weighted_root_upper_lower_conj
      n a w x ε hε
  have hlower : (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
      starRingEnd ℂ (∫ x : ℝ in l..r, f (x + ε * Complex.I)) := by
    calc
      (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
          ∫ x : ℝ in l..r, starRingEnd ℂ (f (x + ε * Complex.I)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hpoint x
      _ = starRingEnd ℂ (∫ x : ℝ in l..r, f (x + ε * Complex.I)) := by
        exact (@RCLike.conjLIE ℂ _).toLinearIsometry.intervalIntegral_comp_comm
          (fun x : ℝ => f (x + ε * Complex.I))
  rw [hlower]
  apply Complex.ext <;> simp <;> ring
