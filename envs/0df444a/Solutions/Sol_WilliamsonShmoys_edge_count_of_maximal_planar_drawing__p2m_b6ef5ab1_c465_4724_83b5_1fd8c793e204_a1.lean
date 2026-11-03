-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:19:36.296365+00:00
-- url     : https://prove2.me/submissions/46cf48b7-4367-46c7-a644-f3431f5f9793

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> Eq L K) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    Eq K.edgeFinset.card (3 * Fintype.card V - 6) := by
  classical
  have h := WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1 K hcard hK hmax
  calc
    K.edgeFinset.card = K.edgeSet.ncard := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    _ = 3 * Fintype.card V - 6 := h.symm
