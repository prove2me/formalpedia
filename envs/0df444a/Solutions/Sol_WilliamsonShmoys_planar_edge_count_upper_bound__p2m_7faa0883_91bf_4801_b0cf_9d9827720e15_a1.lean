-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:20.54125+00:00
-- url     : https://prove2.me/submissions/4bed1069-e6fe-40da-bcc4-22ac3b1e870a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_mono__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hLH, hConnected, hHDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
      L hV hDraw
  have hConnectedBound :=
    WilliamsonShmoys.connected_planar_edge_count_bound__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
      H hV hConnected hHDraw
  have hMono :=
    WilliamsonShmoys.planar_edge_count_mono__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
      L H hLH
  omega