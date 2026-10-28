-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_face_count_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:00:58.363444+00:00
-- url     : https://prove2.me/submissions/23ec1f6f-5c77-41d3-832d-1ec3f0340350

import Mathlib

set_option autoImplicit false

theorem solution (n m f b : ℕ)
    (hEuler : n + f = m + 2)
    (hBoundary : b = 2 * m)
    (hIncidences : 3 * f ≤ b) :
    m + 6 ≤ 3 * n := by
  omega