-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_from_euler_and_triangular_faces
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:36:31.283988+00:00
-- url     : https://prove2.me/submissions/5e5d17b3-883c-4c7f-ab3c-0a86a8ed7ffd

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat)
    (hLarge : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hTriangular : 2 * m = 3 * f) :
    m = 3 * n - 6 := by
  omega