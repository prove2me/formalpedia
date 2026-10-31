-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_edge_arithmetic__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:40.696494+00:00
-- url     : https://prove2.me/submissions/2b7742c7-ff76-4243-81fd-4206658d752f

import Mathlib

theorem solution
    (n e f : ℕ)
    (hn : 3 ≤ n)
    (heuler : n + f = e + 2)
    (hfaces : 3 * f ≤ 2 * e) :
    e ≤ 3 * n - 6 := by
  omega