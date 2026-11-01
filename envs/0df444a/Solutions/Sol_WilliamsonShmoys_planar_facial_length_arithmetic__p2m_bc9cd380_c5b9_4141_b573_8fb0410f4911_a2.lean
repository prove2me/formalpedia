-- Prove2me | solution 1 for WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:16.657201+00:00
-- url     : https://prove2.me/submissions/ac692553-5af9-4145-afc6-2a4b15c8ba45

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem solution
    (n m : ℕ) (hn : 3 ≤ n) (hlower : n ≤ m + 1)
    (hupper : m ≤ 3 * n - 6) :
    ∃ (length : Fin (m + 2 - n) → ℕ),
      2 * m = ∑ i, length i ∧ ∀ i, 3 ≤ length i := by
  have hslots : 0 < m + 2 - n := by omega
  let q : ℕ := m + 1 - n
  have hindex : m + 2 - n = q + 1 := by
    dsimp [q]
    omega
  have hbudget : 3 * q ≤ 2 * m := by
    dsimp [q]
    omega
  have hfirst : 3 ≤ 2 * m - 3 * q := by omega
  rw [hindex]
  refine ⟨Fin.cases (2 * m - 3 * q) (fun _ : Fin q => 3), ?_, ?_⟩
  · rw [Fin.sum_univ_succ]
    simp [Fin.cases, Nat.mul_comm]
    omega
  · intro i
    cases i using Fin.cases with
    | zero =>
        simp [Fin.cases]
        exact hfirst
    | succ j =>
        simp [Fin.cases]