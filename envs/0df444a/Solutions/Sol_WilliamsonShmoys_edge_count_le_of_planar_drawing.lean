-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_le_of_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:21:45.324313+00:00
-- url     : https://prove2.me/submissions/b0a0a787-0f77-4b7b-940c-6d0b466331f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_extend_planar_drawing_connected
import Theorems.Thm_WilliamsonShmoys_edge_count_le_of_connected_planar_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hcard, hconn, hHdraw⟩ :=
    WilliamsonShmoys.extend_planar_drawing_connected G hV hdraw
  exact le_trans hcard
    (WilliamsonShmoys.edge_count_le_of_connected_planar_drawing H hV hHdraw hconn)