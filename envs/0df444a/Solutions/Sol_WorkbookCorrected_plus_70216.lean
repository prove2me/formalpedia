-- Prove2me | solution 1 for WorkbookCorrected.plus_70216
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:28:28.090713+00:00
-- url     : https://prove2.me/submissions/79676654-46a1-4c31-830b-3b557562cb57

import Mathlib

theorem solution (n : ℕ) : (∑ i ∈ Finset.range n, i) = n.choose 2 := by
  rw [Finset.sum_range_id, Nat.choose_two_right]
