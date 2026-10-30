-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:15:58.758008+00:00
-- url     : https://prove2.me/submissions/a3a85348-ce92-4c06-a851-491f96d35eb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hSub, hConnected, hPlanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
      M hV hMplanar
  have hcard : M.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hSub
  calc
    M.edgeSet.ncard + 6 <= H.edgeSet.ncard + 6 := Nat.add_le_add_right hcard 6
    _ <= 3 * Fintype.card V :=
      WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_35749f10_3b92_4bc3_9d25_6f769792d1fb_a2
        H hV hConnected hPlanar