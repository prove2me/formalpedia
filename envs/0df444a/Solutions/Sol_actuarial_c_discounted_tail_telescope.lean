-- Prove2me | solution 1 for actuarial_c_discounted_tail_telescope
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:00:41.320728+00:00
-- url     : https://prove2.me/submissions/0ea313da-8e9a-48ec-b83e-d8efa607f5cc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



theorem solution (s : ℕ → ℝ) (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       (v^j * s j - v^(j+1) * s (j+1))) = s 0 - v^n * s n := by
  induction n with
  | zero => simp []
  | succ n ih => simp only [Finset.sum_range_succ] at *; linarith

