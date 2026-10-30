-- Prove2me | solution 1 for WilliamsonShmoys_euler_list_arithmetic__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:40:24.701001+00:00
-- url     : https://prove2.me/submissions/d76ebd82-efe0-4e7d-ba55-5e377e0aa8a0

import Mathlib

set_option autoImplicit false

theorem solution
    (n m : ℕ)
    (hnm : n ≤ m + 1)
    (hmn : m + 6 ≤ 3 * n) :
    ∃ f : ℕ, ∃ lengths : List ℕ,
      f + n = m + 2 ∧
      lengths.length = f ∧
      lengths.sum = 2 * m ∧
      ∀ x ∈ lengths, 3 ≤ x := by
  let f : ℕ := m + 2 - n
  have hf : 1 ≤ f := by
    dsimp [f]
    omega
  have hthree : 3 * f ≤ 2 * m := by
    dsimp [f]
    omega
  refine ⟨f, List.replicate (f - 1) 3 ++ [2 * m - 3 * (f - 1)], ?_, ?_, ?_, ?_⟩
  · dsimp [f]
    omega
  · simp
    omega
  · simp [List.sum_replicate]
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
    rcases hx with hx | hx
    · omega
    · omega