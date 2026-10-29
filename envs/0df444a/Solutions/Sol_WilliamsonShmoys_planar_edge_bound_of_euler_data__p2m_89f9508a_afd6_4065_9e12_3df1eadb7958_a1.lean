-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:39:03.865903+00:00
-- url     : https://prove2.me/submissions/b3f69231-056d-46fd-bf40-896ccbe6aaba

import Mathlib

theorem solution (n m f : ℕ) (hn : 3 ≤ n) (hEuler : n + f = m + 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega