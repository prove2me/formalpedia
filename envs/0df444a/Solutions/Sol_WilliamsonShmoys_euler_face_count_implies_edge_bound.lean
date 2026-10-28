-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_implies_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:08:38.579372+00:00
-- url     : https://prove2.me/submissions/db7fcfa2-457e-4f10-b995-3059b75b62c4

import Mathlib
set_option autoImplicit false

theorem solution (n m f : Nat) (hEuler : n + f = m + 2) (hFaces : 3 * f <= 2 * m) : m + 6 <= 3 * n := by
  omega
