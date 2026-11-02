-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:50.756411+00:00
-- url     : https://prove2.me/submissions/3834d8c5-c846-4452-b981-f1207305a07f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, ∃ hMdec : DecidableRel M.Adj,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
      L hL
  have hMmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M := by
    intro N hN hMN
    exact hmax N (le_trans hLM hMN) hN
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
      M hM hcard hMmax
  exact ⟨M, inferInstance, hLM, hM, hcount⟩