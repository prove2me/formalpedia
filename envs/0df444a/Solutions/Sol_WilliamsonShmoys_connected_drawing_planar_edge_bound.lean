-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_planar_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:03:37.070277+00:00
-- url     : https://prove2.me/submissions/8006af3b-399b-4783-91f3-e0b72a7820a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawingOn_face_count_euler_and_boundary
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hBoundary⟩ :=
    WilliamsonShmoys.drawingOn_face_count_euler_and_boundary G hconn hdraw hcard
  omega