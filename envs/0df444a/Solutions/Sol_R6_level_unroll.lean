-- Prove2me | solution 1 for R6.level_unroll
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T14:12:29.106985+00:00
-- url     : https://prove2.me/submissions/c2e92679-f977-429f-bcf0-465e4bbb546f

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

theorem solution (E : ℝ) (s : ℕ) (D : ℕ → ℝ) (hs : 2 ≤ s) (hE : 0 ≤ E) (hD0 : 0 ≤ D 0)
    (hstep : ∀ k, D (k + 1) ≤ E + s * D k) :
    ∀ k, D k ≤ (E + D 0) * (2 * (s : ℝ) ^ k - 1) := by
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  intro k
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    have h1 := hstep k
    have h2 : (s : ℝ) * D k ≤ s * ((E + D 0) * (2 * (s : ℝ) ^ k - 1)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : 0 ≤ E + D 0 := by linarith
    rw [pow_succ]
    nlinarith
