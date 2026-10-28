-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_from_crossing_free_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T08:12:20.23672+00:00
-- url     : https://prove2.me/submissions/cfb48ba2-44fe-432b-a90a-c050e53c6add
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_e8dca3ed

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceSides⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count_e8dca3ed
      G hV hConnected hDraw
  omega