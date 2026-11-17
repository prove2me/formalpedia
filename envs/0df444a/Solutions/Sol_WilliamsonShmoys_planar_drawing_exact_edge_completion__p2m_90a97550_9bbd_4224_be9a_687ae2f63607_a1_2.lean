-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T08:02:30.176841+00:00
-- url     : https://prove2.me/submissions/984ff378-976e-4066-b501-d237d68af5d7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, ∃ hMdec : DecidableRel M.Adj,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1 L hL
  refine ⟨M, Classical.decRel M.Adj, hLM, hM, ?_⟩
  exact @WilliamsonShmoys.maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
    V _ _ M (Classical.decRel M.Adj) hM hcard (fun N hN hMN => hmax N hMN hN)
