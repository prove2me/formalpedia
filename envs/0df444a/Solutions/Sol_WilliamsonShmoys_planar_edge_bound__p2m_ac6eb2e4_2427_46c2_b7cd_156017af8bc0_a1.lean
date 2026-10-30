-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:07.667248+00:00
-- url     : https://prove2.me/submissions/b92bec55-d8ce-42b0-8868-794919036175
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hConnected, hHDrawing, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_connected_augmentation__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
      G hDraw hCard
  have hBound :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
      H hHDrawing hConnected hCard
  omega