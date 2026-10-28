-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_euler_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:13:57.402979+00:00
-- url     : https://prove2.me/submissions/407bce81-59b7-49a7-8751-7aa5f1c52d22

import Mathlib

set_option autoImplicit false

theorem solution (v e f : Nat) (hEuler : v + f = e + 2)
    (hFaceDegrees : 3 * f <= 2 * e) (hv : 3 <= v) : e <= 3 * v - 6 := by
  omega