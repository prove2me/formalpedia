-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_21c51033_6ced_4e68_8653_efea3430d001_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:04.529093+00:00
-- url     : https://prove2.me/submissions/7023b0b7-c05d-4036-a007-25723f15a158
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hHDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
      G hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
      H hHDraw hV hMax
  exact ⟨H, hGH, hCount⟩