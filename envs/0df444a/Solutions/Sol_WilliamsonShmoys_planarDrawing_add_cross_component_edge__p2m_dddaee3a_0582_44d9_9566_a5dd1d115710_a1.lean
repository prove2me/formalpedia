-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_add_cross_component_edge__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:32.218667+00:00
-- url     : https://prove2.me/submissions/4d6157ee-f041-436a-a5b7-ffb5cadc793d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
import Theorems.Thm_WilliamsonShmoys_planarDrawing_add_edge_of_not_reachable__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v ∧
      ∃ H : SimpleGraph V,
        G ≤ H ∧
        H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
        WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
      G hdisconnected
  obtain ⟨H, hGH, hEdges, hH⟩ :=
    WilliamsonShmoys.planarDrawing_add_edge_of_not_reachable__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
      G hG u v huv
  exact ⟨u, v, huv, H, hGH, hEdges, hH⟩