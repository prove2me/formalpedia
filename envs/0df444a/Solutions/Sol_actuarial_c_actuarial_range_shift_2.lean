-- Prove2me | solution 2 for actuarial_c_actuarial_range_shift
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:23:41.203536+00:00
-- url     : https://prove2.me/submissions/611b7f54-bd02-41c8-a201-235dd2f5a3c7

import Mathlib
set_option autoImplicit false

theorem solution (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), f j) =
      f 0 + ∑ j ∈ Finset.range n, f (j+1) := by
  rw [Finset.sum_range_succ']
  ring
