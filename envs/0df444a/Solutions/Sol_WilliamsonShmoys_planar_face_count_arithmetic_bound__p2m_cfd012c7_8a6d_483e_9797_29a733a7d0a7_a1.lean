-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic_bound__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:22.256784+00:00
-- url     : https://prove2.me/submissions/36eb9096-271d-4cda-938c-10c624943ced

import Mathlib

theorem solution (n m : ℕ) (hn : 3 ≤ n) (f : ℤ)
    (heuler : (n : ℤ) - (m : ℤ) + f = 2)
    (hinc : 3 * f ≤ 2 * (m : ℤ)) : m ≤ 3 * n - 6 := by
  omega