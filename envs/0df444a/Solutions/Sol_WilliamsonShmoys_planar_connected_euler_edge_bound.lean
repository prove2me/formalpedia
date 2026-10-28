-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_euler_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:00:40.837212+00:00
-- url     : https://prove2.me/submissions/d1220008-822d-4c68-be4c-1945c9c57613
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_bounds
import Theorems.Thm_WilliamsonShmoys_euler_face_count_implies_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_bounds G hG hconn hcard
  exact WilliamsonShmoys.euler_face_count_implies_edge_bound
    (Fintype.card V) G.edgeSet.ncard f hEuler hFaces