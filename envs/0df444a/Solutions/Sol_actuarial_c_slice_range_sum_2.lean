-- Prove2me | solution 2 for actuarial_c_slice_range_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:13:39.39778+00:00
-- url     : https://prove2.me/submissions/f435456a-aa17-408a-ad30-94b6c4b54da4

import Mathlib
set_option autoImplicit false

theorem solution (h a n : ℕ) (f : ℕ → ℝ)
    (han : a+n ≤ h) :
    (∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then f j else 0) =
       ∑ j ∈ Finset.range n, f (a+j) := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range h).filter (fun j => a ≤ j ∧ j < a+n) = Finset.Ico a (a+n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
  rw [hf, Finset.sum_Ico_eq_sum_range]
  simp
