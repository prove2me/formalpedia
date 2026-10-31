-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:58.85085+00:00
-- url     : https://prove2.me/submissions/7dad4699-e400-46a4-989d-db5455062e27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_supergraph__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hConn, hDraw, hEdge⟩ :=
    WilliamsonShmoys.planar_drawing_has_connected_supergraph__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1 H hH
  exact hEdge.trans
    (WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a1 G hCard hConn hDraw)