-- Prove2me | solution 1 for RhinViola.scaledReciprocalSquareNat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:18:18.55022+00:00
-- url     : https://prove2.me/submissions/4ec581b9-46c4-46f4-bcb6-35505d795122

import Theorems.Thm_RhinViola_scaledReciprocalProductNat
import Mathlib.Tactic

theorem solution
    (D r : ℕ) (hr : r ∣ D) (hrpos : 0 < r) :
    (D : ℝ) ^ 2 * ((1 : ℝ) / ((r : ℝ) ^ 2)) =
      ((((D / r) ^ 2 : ℕ) : ℝ)) := by
  have hrR : 0 < (r : ℝ) := by
    exact_mod_cast hrpos
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hp :=
    RhinViola.scaledReciprocalProductNat
      D r r hr hr hrpos hrpos
  calc
    (D : ℝ) ^ 2 * ((1 : ℝ) / ((r : ℝ) ^ 2)) =
        (D : ℝ) ^ 2 * ((1 : ℝ) / (r : ℝ)) *
          ((1 : ℝ) / (r : ℝ)) := by
      field_simp [hr0] <;> ring
    _ = ((((D / r) * (D / r) : ℕ) : ℝ)) := hp
    _ = ((((D / r) ^ 2 : ℕ) : ℝ)) := by
      rw [pow_two]
