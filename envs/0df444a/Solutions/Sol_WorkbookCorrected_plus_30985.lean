-- Prove2me | solution 1 for WorkbookCorrected.plus_30985
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:28:27.197294+00:00
-- url     : https://prove2.me/submissions/a8c655fc-9f35-4bb4-a235-8699a94598a1

import Mathlib

theorem solution : ∀ n : ℕ, Nat.choose n 0 + Nat.choose n 1 = Nat.choose (n + 1) 1 := by
  intro n
  simp [Nat.choose_one_right, Nat.add_comm]
