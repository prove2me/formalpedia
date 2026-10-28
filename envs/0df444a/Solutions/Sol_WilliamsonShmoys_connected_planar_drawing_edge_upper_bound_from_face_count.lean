-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_from_face_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:00:34.719277+00:00
-- url     : https://prove2.me/submissions/aefd7427-9c12-458b-a252-bd89ea69e895

import Mathlib

set_option autoImplicit false


theorem solution
    (v e f : ℕ) (hv : 3 <= v)
    (hEuler : v + f = e + 2)
    (hFaces : 3 * f <= 2 * e) :
    e + 6 <= 3 * v := by
  omega
