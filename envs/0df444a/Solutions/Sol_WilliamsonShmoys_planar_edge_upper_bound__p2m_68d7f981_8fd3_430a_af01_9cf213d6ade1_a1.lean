-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:44:28.287985+00:00
-- url     : https://prove2.me/submissions/92f4a835-367a-4329-bf67-730168a3ec57

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨M, hGM, hMDraw, hMMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
      G hDraw
  have hMCount :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
      M hV hMDraw hMMax
  have hEdgeCount : G.edgeSet.ncard ≤ M.edgeSet.ncard := by
    apply Set.ncard_mono
    exact SimpleGraph.edgeSet_mono hGM
  omega