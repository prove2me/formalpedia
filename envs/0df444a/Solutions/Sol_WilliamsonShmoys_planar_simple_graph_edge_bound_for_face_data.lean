-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:11:56.581367+00:00
-- url     : https://prove2.me/submissions/efd3b152-171a-4678-ab93-cf6ee4461884

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_gives_face_data
import Theorems.Thm_WilliamsonShmoys_face_data_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.face_data_edge_bound J
    (WilliamsonShmoys.planar_drawing_on_gives_face_data J hConn hV hJ)