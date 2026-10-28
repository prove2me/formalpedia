-- Prove2me | solution 1 for WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:29:08.10492+00:00
-- url     : https://prove2.me/submissions/fb6cc7cc-14fa-4b99-a19f-84c216991a60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_count_inequality_of_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceLength⟩ :=
    WilliamsonShmoys.planar_face_count_inequality_of_drawing
      L hV hconn hdraw
  omega