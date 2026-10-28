-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:16:44.923629+00:00
-- url     : https://prove2.me/submissions/8f10298f-ae53-4646-b4d7-25c47f57a8c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_simple_planar_graph_edge_bound_of_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L)
    (f : ℕ)
    (heuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f ≤ 2 * L.edgeSet.ncard := by
  have hplanar := WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing L hV hconn hdraw
  omega