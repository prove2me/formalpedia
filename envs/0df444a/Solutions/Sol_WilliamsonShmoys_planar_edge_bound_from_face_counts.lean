-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_face_counts
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:10:38.345697+00:00
-- url     : https://prove2.me/submissions/e1562e3d-b263-4476-9968-a38565b67c42

import Mathlib

theorem solution
    (n e f : Nat)
    (hEuler : n + f = e + 2)
    (hFaceIncidence : 3 * f ≤ 2 * e) :
    e + 6 ≤ 3 * n := by
  omega