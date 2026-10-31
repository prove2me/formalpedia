-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:42:19.89614+00:00
-- url     : https://prove2.me/submissions/c06da2ad-203e-4b27-a2f6-a31db393b31b

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_via_triangulation

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_via_triangulation K hCard hK hmax
