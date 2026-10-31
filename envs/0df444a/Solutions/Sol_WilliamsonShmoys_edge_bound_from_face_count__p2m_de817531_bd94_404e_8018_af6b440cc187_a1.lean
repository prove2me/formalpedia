-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:24:51.550544+00:00
-- url     : https://prove2.me/submissions/6290c99d-e748-4faf-8896-532e381562a8

import Mathlib

theorem solution (n e F B : Nat) (hCard : 3 ≤ n) (hEuler : n + F = e + 2)
    (hDarts : B = 2 * e) (hBoundary : 3 * F ≤ B) : e ≤ 3 * n - 6 := by
  omega