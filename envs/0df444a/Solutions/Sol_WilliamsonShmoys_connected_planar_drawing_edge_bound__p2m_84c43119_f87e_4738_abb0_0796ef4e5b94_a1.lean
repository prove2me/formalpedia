-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:22:38.65265+00:00
-- url     : https://prove2.me/submissions/d02c5a3c-98fd-40af-b43c-8aeb166bad4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hConn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨F, B, hEuler, hDarts, hBoundary⟩ :=
    WilliamsonShmoys.connected_planar_drawing_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
      G hCard hConn hG
  exact WilliamsonShmoys.edge_bound_from_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
    (Fintype.card V) G.edgeSet.ncard F B hCard hEuler hDarts hBoundary