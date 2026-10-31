-- Prove2me | solution 2 for WilliamsonShmoys.inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:21:33.087604+00:00
-- url     : https://prove2.me/submissions/af4b6718-fe75-41b7-844c-4dd261a353b8

import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1 H hH hCard hmax
