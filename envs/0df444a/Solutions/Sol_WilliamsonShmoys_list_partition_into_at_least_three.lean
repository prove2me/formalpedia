-- Prove2me | solution 1 for WilliamsonShmoys.list_partition_into_at_least_three
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:45:24.712802+00:00
-- url     : https://prove2.me/submissions/ccc4f1a2-4e10-403e-94d8-cd97ad5970e7

import Mathlib

theorem solution : ¬ (∀ {α : Type} (xs : List α) (k : Nat)
    (hcapacity : 3 * k ≤ xs.length),
    ∃ fs : List (List α),
      fs.length = k ∧
      List.Perm fs.flatten xs ∧
      (∀ face ∈ fs, ∀ x ∈ face, x ∈ xs) ∧
      3 * k ≤ (fs.map List.length).sum ∧
      (fs.map List.length).sum = xs.length) := by
  intro h
  obtain ⟨fs, hl, hp, -, -, -⟩ := h (α := Unit) [()] 0 (by simp)
  rw [List.length_eq_zero_iff] at hl
  subst hl
  simpa using hp.length_eq
