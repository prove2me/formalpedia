-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:35.025881+00:00
-- url     : https://prove2.me/submissions/195e9412-48db-4934-9434-99a42babe4be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1 K hCard hK
  have hlower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1 K hCard hK hmax
  omega