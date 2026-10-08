-- Prove2me | solution 1 for RhinViola.scaledReciprocalProductNat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:06:56.157994+00:00
-- url     : https://prove2.me/submissions/66f928cc-16ae-4a51-af1c-72fd5294a8fc

import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic

theorem solution
    (D r s : ℕ) (hr : r ∣ D) (hs : s ∣ D)
    (hrpos : 0 < r) (hspos : 0 < s) :
    (D : ℝ) ^ 2 * ((1 : ℝ) / (r : ℝ)) * ((1 : ℝ) / (s : ℝ)) =
      ((((D / r) * (D / s) : ℕ) : ℝ)) := by
  have hrR : 0 < (r : ℝ) := by
    exact_mod_cast hrpos
  have hsR : 0 < (s : ℝ) := by
    exact_mod_cast hspos
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hsR
  rw [Nat.cast_mul, Nat.cast_div_charZero hr, Nat.cast_div_charZero hs]
  field_simp [hr0, hs0] <;> ring
