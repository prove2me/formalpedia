-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_bound_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:48:53.650576+00:00
-- url     : https://prove2.me/submissions/ebc0e3d3-6e7a-41fb-903f-aa75725776fc

import Mathlib

set_option autoImplicit false

theorem solution
    (m n f : Nat)
    (hEuler : m + 2 = n + f)
    (hFaces : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by
  omega