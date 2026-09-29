-- Prove2me | solution 1 for WorkbookCorrected.plus_69256
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:36:27.212901+00:00
-- url     : https://prove2.me/submissions/9f2fc67f-072f-4ad3-a15b-48c450c06e82

import Mathlib

theorem solution (n m : ℕ) : ∑ k ∈ Finset.range (m+1), Nat.choose (n + k) k = Nat.choose (n + m + 1) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show n + (m + 1) + 1 = (n + m + 1) + 1 from by ring]
    rw [show n + (m + 1) = n + m + 1 from by ring]
    exact (Nat.choose_succ_succ' (n + m + 1) m).symm
