-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:40.404542+00:00
-- url     : https://prove2.me/submissions/8eebc168-7b65-4863-9fd2-bdfb95915609

import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_maximal_graph_edge_count_391f3239_9f51_4455_9b2f_cbbc61103aca G hV hG hmax
