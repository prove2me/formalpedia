-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:45:55.266969+00:00
-- url     : https://prove2.me/submissions/9192623a-8f7b-422a-b6d2-2730c5c7305f

import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_for_exact_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet :=
  WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exact_count H hH
