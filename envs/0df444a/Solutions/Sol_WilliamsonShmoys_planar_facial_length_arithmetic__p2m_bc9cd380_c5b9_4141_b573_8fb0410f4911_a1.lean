-- Prove2me | solution 1 for WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:48:37.601989+00:00
-- url     : https://prove2.me/submissions/44d948d3-bfa5-4ffb-8c20-1eb9d9b164e3

import Theorems.Thm_WilliamsonShmoys_planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem solution
    (n m : ℕ) (hn : 3 ≤ n) (hlower : n ≤ m + 1)
    (hupper : m ≤ 3 * n - 6) :
    ∃ (length : Fin (m + 2 - n) → ℕ),
      2 * m = ∑ i, length i ∧ ∀ i, 3 ≤ length i :=
  WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2 n m hn hlower hupper