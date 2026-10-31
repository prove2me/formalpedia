-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:30:11.085067+00:00
-- url     : https://prove2.me/submissions/a11dcc2a-77a0-4d22-8c31-863c6674818d

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound L hL hCard
