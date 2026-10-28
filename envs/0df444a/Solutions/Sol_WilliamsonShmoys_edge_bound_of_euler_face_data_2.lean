-- Prove2me | solution 2 for WilliamsonShmoys.edge_bound_of_euler_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:30:16.735234+00:00
-- url     : https://prove2.me/submissions/4a93daf0-124a-42f0-b4bb-694e2698036f

import Mathlib

theorem solution (v e f : ℕ) (hEuler : v + f = e + 2) (hFaceDegrees : 3 * f <= 2 * e)
    (hv : 3 <= v) : e <= 3 * v - 6 := by
  omega
