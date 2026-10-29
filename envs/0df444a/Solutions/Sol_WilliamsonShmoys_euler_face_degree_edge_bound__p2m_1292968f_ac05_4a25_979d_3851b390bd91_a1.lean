-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_degree_edge_bound__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:30.695305+00:00
-- url     : https://prove2.me/submissions/0c0a40b8-ea45-4c6c-9ce1-7976502f058b

import Mathlib

theorem solution
    (n m e s : ℕ)
    (hEuler : n + m = e + 2)
    (hSum : s = 2 * e)
    (hFaces : 3 * m ≤ s) :
    e + 6 ≤ 3 * n := by
  omega
