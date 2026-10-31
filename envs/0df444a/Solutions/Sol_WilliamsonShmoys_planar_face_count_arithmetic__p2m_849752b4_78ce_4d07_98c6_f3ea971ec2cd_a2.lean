-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:51.270434+00:00
-- url     : https://prove2.me/submissions/4922c5ab-3f27-47c1-ab5c-3a11c884406f

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : ℕ)
    (hn : 3 ≤ n)
    (hEuler : (n : ℤ) - (m : ℤ) + (f : ℤ) = 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega