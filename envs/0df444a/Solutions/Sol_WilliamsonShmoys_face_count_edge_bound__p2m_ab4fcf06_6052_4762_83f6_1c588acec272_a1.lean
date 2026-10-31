-- Prove2me | solution 1 for WilliamsonShmoys.face_count_edge_bound__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:26.914394+00:00
-- url     : https://prove2.me/submissions/de420e8c-049f-403c-a631-c7aefb210410

import Mathlib

set_option autoImplicit false

theorem solution (v e : ℕ) (F : Type) [Fintype F] (length : F → ℕ)
    (hv : 3 ≤ v)
    (hsum : (∑ f : F, length f) = 2 * e)
    (hlen : ∀ f : F, 3 ≤ length f)
    (heuler : v + Fintype.card F = e + 2) : e + 6 ≤ 3 * v := by
  have hfaces : 3 * Fintype.card F ≤ ∑ f : F, length f := by
    calc
      3 * Fintype.card F = ∑ _f : F, 3 := by simp [mul_comm]
      _ ≤ ∑ f : F, length f := by
        apply Finset.sum_le_sum
        intro f hf
        exact hlen f
  omega