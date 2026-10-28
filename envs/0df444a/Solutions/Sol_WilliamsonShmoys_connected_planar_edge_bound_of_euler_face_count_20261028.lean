-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_of_euler_face_count_20261028
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:11:47.534731+00:00
-- url     : https://prove2.me/submissions/e887d288-847c-42b1-a061-134e102ca392

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (F : ℕ)
    (hEuler : Fintype.card V + F = G.edgeSet.ncard + 2)
    (hFaces : 3 * F ≤ 2 * G.edgeSet.ncard) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  omega
