-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:48.535791+00:00
-- url     : https://prove2.me/submissions/cfe1a83f-1819-450f-ac28-4e5156c216cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_completion__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (hHdec : DecidableRel H.Adj),
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := hHdec
       3 * Fintype.card V - 6 = H.edgeFinset.card) := by
  obtain ⟨M, hKM, hMdraw, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_completion__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2 K hK
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  refine ⟨M, Classical.decRel M.Adj, hKM, hMdraw, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
    M hMdraw hcard (fun L hML hLdraw => hmax L (hKM.trans hML) hLdraw)