-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:23:39.667272+00:00
-- url     : https://prove2.me/submissions/c666a7f2-7e19-4130-addb-497adbb3c01c

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
