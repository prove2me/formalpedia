-- Prove2me | solution 2 for actuarial_c_discounted_tail_telescope
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T12:13:26.156522+00:00
-- url     : https://prove2.me/submissions/2eef1e9e-e7b3-41e4-b338-f2c3665f7718

import Mathlib
set_option autoImplicit false

theorem solution (s : ℕ → ℝ) (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       (v^j * s j - v^(j+1) * s (j+1))) = s 0 - v^n * s n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring
