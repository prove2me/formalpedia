-- Prove2me | solution 1 for WilliamsonShmoys.face_count_arithmetic__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:56:33.044201+00:00
-- url     : https://prove2.me/submissions/5923f254-ac84-4aeb-b4c4-2aff1f5f8b5b

import Mathlib

theorem solution
    (n m f : ℕ)
    (hEuler : n + f = m + 2)
    (hFaceLength : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by
  omega