-- Prove2me | solution 1 for WorkbookCorrected.plus_36538
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:36:26.297492+00:00
-- url     : https://prove2.me/submissions/b4b32a2d-899b-4277-9d5d-fb14bbdc9139

import Mathlib

theorem solution (n r : ℕ) : ∑ k ∈ Finset.range (r + 1), Nat.choose (n + k) k = Nat.choose (n + r + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show n + (r + 1) + 1 = (n + r + 1) + 1 from by ring]
    rw [show n + (r + 1) = n + r + 1 from by ring]
    exact (Nat.choose_succ_succ' (n + r + 1) r).symm
