-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_ea8ef902_b5b0_4092_a824_9484bf1d76fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:59:13.920565+00:00
-- url     : https://prove2.me/submissions/6d866966-2a6c-4700-8088-d4ece3763803

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : LE.le 3 (Fintype.card V))
    (hKdraw : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> L = K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have h := WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1 K hcard hKdraw hmax
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at h
  omega
