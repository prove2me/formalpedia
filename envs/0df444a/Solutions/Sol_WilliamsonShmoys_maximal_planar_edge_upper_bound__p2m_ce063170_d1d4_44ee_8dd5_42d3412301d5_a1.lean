-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ce063170_d1d4_44ee_8dd5_42d3412301d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:43.325478+00:00
-- url     : https://prove2.me/submissions/7f0de88a-a948-4391-96a8-00d8dc1b1b41

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1
    L hL hcard
