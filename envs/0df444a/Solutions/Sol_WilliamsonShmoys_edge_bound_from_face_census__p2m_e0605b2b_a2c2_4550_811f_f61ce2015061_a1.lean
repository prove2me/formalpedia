-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:19.8874+00:00
-- url     : https://prove2.me/submissions/55edc814-5e12-481e-9ad0-61a70b1f1801

import Mathlib

theorem solution
    (n m f : ℕ)
    (heuler : n + f = m + 2)
    (hfaces : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by
  omega