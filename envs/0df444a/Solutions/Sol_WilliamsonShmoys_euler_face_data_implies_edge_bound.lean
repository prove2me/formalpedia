-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_data_implies_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:12:29.125845+00:00
-- url     : https://prove2.me/submissions/42356240-70fe-4e62-80a3-3cd3cd261f39

import Mathlib

set_option autoImplicit false

theorem solution
    {n m f c : ℕ}
    (hn : 3 ≤ n)
    (hm : 2 ≤ m)
    (heuler : n + f = m + c + 1)
    (hc : 1 ≤ c)
    (hdegree : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by
  omega