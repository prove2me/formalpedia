-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_count_completion__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:05:48.633209+00:00
-- url     : https://prove2.me/submissions/8a9fb60e-0a50-4063-97f8-95799e310fe1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hPlanar, hMax⟩ :=
    WilliamsonShmoys.exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1 L hDraw
  refine ⟨M, hLM, hPlanar, ?_⟩
  exact WilliamsonShmoys.maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1 M hPlanar hMax hV