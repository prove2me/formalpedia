-- Prove2me | solution 1 for RhinViola.scaledReciprocalSquareBlockNat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T10:23:20.902596+00:00
-- url     : https://prove2.me/submissions/bc73be27-bdff-414d-b40f-f0260182b5e8

import Theorems.Thm_RhinViola_scaledReciprocalSquareNat
import Mathlib.Tactic

theorem solution
    (D h : ℕ)
    (hdiv : ∀ j : ℕ, j < h → j + 1 ∣ D) :
    (D : ℝ) ^ 2 *
        (Finset.sum (Finset.range h) (fun j : ℕ =>
          (1 : ℝ) / ((((j + 1 : ℕ) : ℝ)) ^ 2))) =
      ((Finset.sum (Finset.range h) (fun j : ℕ =>
          (D / (j + 1)) ^ 2) : ℕ) : ℝ) := by
  calc
    (D : ℝ) ^ 2 *
        (Finset.sum (Finset.range h) (fun j : ℕ =>
          (1 : ℝ) / ((((j + 1 : ℕ) : ℝ)) ^ 2))) =
      Finset.sum (Finset.range h) (fun j : ℕ =>
        (D : ℝ) ^ 2 *
          ((1 : ℝ) / ((((j + 1 : ℕ) : ℝ)) ^ 2))) := by
      rw [Finset.mul_sum]
    _ = Finset.sum (Finset.range h) (fun j : ℕ =>
          ((((D / (j + 1)) ^ 2 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact RhinViola.scaledReciprocalSquareNat
        D (j + 1) (hdiv j (Finset.mem_range.mp hj)) (by omega)
    _ = ((Finset.sum (Finset.range h) (fun j : ℕ =>
          (D / (j + 1)) ^ 2) : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
