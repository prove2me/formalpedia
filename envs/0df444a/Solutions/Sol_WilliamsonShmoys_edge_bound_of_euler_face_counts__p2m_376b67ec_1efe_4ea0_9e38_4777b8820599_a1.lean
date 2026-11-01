-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:20.519116+00:00
-- url     : https://prove2.me/submissions/f6af2c62-aeea-46dc-980c-2b8f5f58306c

import Mathlib

theorem solution (n m f : ℕ)
    (hEuler : n + f = m + 2)
    (hfaces : 3 * f ≤ 2 * m)
    (hn : 3 ≤ n) :
    m ≤ 3 * n - 6 := by
  omega