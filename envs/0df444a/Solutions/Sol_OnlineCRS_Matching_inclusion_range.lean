-- Prove2me | solution 1 for OnlineCRS.Matching.inclusion_range
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:40.294865+00:00
-- url     : https://prove2.me/submissions/2c361b1c-bb9a-4a80-863a-a6e633fb68d8

import Mathlib

set_option autoImplicit false

theorem solution (t : ℝ) (ht : 0 < t) :
    0 ≤ (1 - Real.exp (-t)) / t ∧ (1 - Real.exp (-t)) / t ≤ 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
  refine ⟨div_nonneg (by linarith) ht.le, ?_⟩
  rw [div_le_one ht]
  linarith
