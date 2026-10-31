-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:36:41.761977+00:00
-- url     : https://prove2.me/submissions/565e2581-3684-4212-aa8e-ac2a2d4613ca

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_graph_edge_bound_e51c1790 M hV hM
