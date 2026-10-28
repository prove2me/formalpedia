-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_arithmetic_afa305d5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:46:21.649285+00:00
-- url     : https://prove2.me/submissions/53031117-0533-47a4-abb9-6ff26c272d5f

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat)
    (hEuler : n + f = m + 2)
    (hIncidence : 2 * m = 3 * f) :
    3 * n <= m + 6 := by
  omega