-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:58:15.976262+00:00
-- url     : https://prove2.me/submissions/73a0c31e-93a7-4b47-b24a-7d50d90c3b38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_nonempty_planar_drawing__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
import Theorems.Thm_WilliamsonShmoys_connected_drawing_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hConn, hDraw, hEdge⟩ :=
    WilliamsonShmoys.connected_supergraph_of_nonempty_planar_drawing__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2 H hCard hH
  exact hEdge.trans
    (WilliamsonShmoys.edge_bound_from_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
      (Fintype.card V) G.edgeSet.ncard hCard
      (WilliamsonShmoys.connected_drawing_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
        G hCard hConn hDraw))