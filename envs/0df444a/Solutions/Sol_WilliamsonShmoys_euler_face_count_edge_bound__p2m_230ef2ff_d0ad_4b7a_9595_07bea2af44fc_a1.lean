-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_edge_bound__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:36:28.256583+00:00
-- url     : https://prove2.me/submissions/f0fa9752-3b46-4eab-9b60-0cd47520f6e4

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem solution {v e f : ℕ} (ell : Fin f → ℕ)
    (hEuler : v + f = e + 2)
    (hsum : (∑ i : Fin f, ell i) = 2 * e)
    (hlen : ∀ i, 3 ≤ ell i) : e + 6 ≤ 3 * v := by
  have hlower : 3 * f ≤ ∑ i : Fin f, ell i := by
    calc
      3 * f = f * 3 := Nat.mul_comm _ _
      _ = ∑ _i : Fin f, (3 : ℕ) := by simp
      _ ≤ ∑ i : Fin f, ell i := Finset.sum_le_sum fun i _ => hlen i
  omega