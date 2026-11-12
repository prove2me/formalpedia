-- Prove2me | solution 1 for RhinViola.scaledDiagonalHarmonicRangeLcm
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:23:31.607301+00:00
-- url     : https://prove2.me/submissions/9e13c338-f2c6-498a-836c-e6e14dac0a3c

import Mathlib

set_option autoImplicit false

/-- Scaling a harmonic square sum by the square of the range lcm clears all denominators. -/
theorem solution (n h : ℕ) (hhn : h < n) :
    let D := (Finset.range n).lcm (fun i : ℕ => i + 1)
    (D : ℝ) ^ 2 *
        (Finset.sum (Finset.range h) (fun j : ℕ =>
          (1 : ℝ) / ((((j + 1 : ℕ) : ℝ)) ^ 2))) =
      ((Finset.sum (Finset.range h) (fun j : ℕ =>
          (D / (j + 1)) ^ 2) : ℕ) : ℝ) := by
  classical
  dsimp only
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ∈ Finset.range n := by
    rw [Finset.mem_range] at hj ⊢
    omega
  have hdvd : (j + 1) ∣ (Finset.range n).lcm (fun i : ℕ => i + 1) :=
    Finset.dvd_lcm (f := fun i : ℕ => i + 1) hjn
  rw [Nat.cast_pow, Nat.cast_div_charZero hdvd]
  rw [div_pow]
  ring
