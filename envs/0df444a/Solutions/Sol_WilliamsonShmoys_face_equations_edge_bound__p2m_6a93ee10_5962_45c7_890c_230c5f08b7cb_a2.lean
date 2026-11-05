-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_edge_bound__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:08:14.858767+00:00
-- url     : https://prove2.me/submissions/cf243777-61da-47c4-8010-da07abc74bd8

import Mathlib

theorem solution (n m f : Nat) (hn : 3 <= n)
    (hEuler : n + f = m + 2) (hIncidence : 3 * f = 2 * m) :
    3 * n - 6 <= m := by
  omega
