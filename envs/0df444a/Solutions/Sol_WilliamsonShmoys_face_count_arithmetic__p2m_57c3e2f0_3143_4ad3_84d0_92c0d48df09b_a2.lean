-- Prove2me | solution 1 for WilliamsonShmoys.face_count_arithmetic__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:00.391782+00:00
-- url     : https://prove2.me/submissions/b6d364b8-938e-4f70-b52c-5d479f97f533

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat) (hn : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega