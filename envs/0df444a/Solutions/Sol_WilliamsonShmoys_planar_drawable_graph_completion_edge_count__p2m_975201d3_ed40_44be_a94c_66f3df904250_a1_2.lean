-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawable_graph_completion_edge_count__p2m_975201d3_ed40_44be_a94c_66f3df904250_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:02:30.224786+00:00
-- url     : https://prove2.me/submissions/a4479314-ff0d-47d2-85c0-795bfac2de10

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
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
  obtain ⟨M, hKM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1 K hK
  refine ⟨M, Classical.decRel M.Adj, hKM, hM, ?_⟩
  exact @WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
    V _ _ M (Classical.decRel M.Adj) hM hcard hmax
