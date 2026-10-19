-- Prove2me | solution 2 for actuarial_c_discounted_survival_annuity_conservation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:21:04.82851+00:00
-- url     : https://prove2.me/submissions/acb4af57-f9e9-4260-b698-cf3693be5fd9

import Mathlib
set_option autoImplicit false

theorem solution (s : ℕ → ℝ)
    (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       v^(j+1) * (s j - s (j+1))) +
      (1-v)*(∑ j ∈ Finset.range n, v^j * s j) +
      v^n * s n = s 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => v^j * s j) k]
    have h : v^(k+1) = v^k * v := pow_succ v k
    rw [h] at *
    nlinarith [ih]
