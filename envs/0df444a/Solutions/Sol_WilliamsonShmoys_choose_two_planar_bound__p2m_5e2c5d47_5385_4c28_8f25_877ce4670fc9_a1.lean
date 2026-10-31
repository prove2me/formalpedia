-- Prove2me | solution 1 for WilliamsonShmoys.choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:44:13.708994+00:00
-- url     : https://prove2.me/submissions/ef157806-a69e-4b41-9fe7-57e139cc481d

import Theorems.Thm_WilliamsonShmoys_choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ)
    (hcard : 3 ≤ n)
    (hedges : n.choose 2 ≤ 3 * n - 6) :
    n ≤ 4 :=
  WilliamsonShmoys.choose_two_planar_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2 n hcard hedges
