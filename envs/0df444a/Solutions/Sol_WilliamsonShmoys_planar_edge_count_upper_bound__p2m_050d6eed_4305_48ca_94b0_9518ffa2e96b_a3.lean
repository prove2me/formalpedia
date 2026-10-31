-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:10:15.025644+00:00
-- url     : https://prove2.me/submissions/add63928-2755-4e9a-abf6-205e46460044

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    T.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound T hT hV
