-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_data_implies_edge_bound__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:08.278655+00:00
-- url     : https://prove2.me/submissions/0758d758-d07f-4f68-81f9-4cd047cb10da

import Mathlib

set_option autoImplicit false

theorem solution (n m M f : ℕ) (hn : 3 ≤ n) (hm : m ≤ M)
    (heuler : n + f = M + 2) (hfaces : 3 * f ≤ 2 * M) :
    m + 6 ≤ 3 * n := by
  omega