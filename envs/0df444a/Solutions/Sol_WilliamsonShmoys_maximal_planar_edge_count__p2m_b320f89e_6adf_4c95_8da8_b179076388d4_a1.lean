-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:30:35.17517+00:00
-- url     : https://prove2.me/submissions/b8e39cd6-5f6d-4f0a-bd7f-925771224713

import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_graph_edge_count N hN hCard hmax
