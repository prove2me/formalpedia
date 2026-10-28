-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_edge_count_from_face_equations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:32:32.893049+00:00
-- url     : https://prove2.me/submissions/e6e510d4-c2c2-4f42-af94-b86b339c4be4

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : ℕ) (hCard : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hIncidence : 3 * f = 2 * m) :
    m = 3 * n - 6 := by
  omega