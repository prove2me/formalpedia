-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_implies_simple_edge_bound__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:24.946835+00:00
-- url     : https://prove2.me/submissions/9a05e2c2-2d21-4ae0-964e-e6da12a51834

import Mathlib

set_option autoImplicit false

theorem solution
    (n f e : ℕ) (length : Fin f → ℕ)
    (hEuler : n + f = e + 2)
    (hIncidence : 2 * e = ∑ i, length i)
    (hLength : ∀ i, 3 ≤ length i) :
    e + 6 ≤ 3 * n := by
  have hsum : 3 * f ≤ ∑ i : Fin f, length i := by
    calc
      3 * f = ∑ _i : Fin f, (3 : ℕ) := by
        simp [Finset.sum_const, Finset.card_fin, Nat.mul_comm]
      _ ≤ ∑ i : Fin f, length i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hLength i
  have hfaces : 3 * f ≤ 2 * e := by
    calc
      3 * f ≤ ∑ i : Fin f, length i := hsum
      _ = 2 * e := hIncidence.symm
  omega