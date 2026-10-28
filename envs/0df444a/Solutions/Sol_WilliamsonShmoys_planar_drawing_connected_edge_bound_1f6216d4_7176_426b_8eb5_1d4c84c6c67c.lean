-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_edge_bound_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:22:45.519991+00:00
-- url     : https://prove2.me/submissions/878b65f4-77e2-4cd4-9348-4638a37db968
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data_for_edge_bound_1f6216d4
import Theorems.Thm_WilliamsonShmoys_face_count_edge_bound_1f6216d4

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨F, degree, heuler, hsum, hdegree⟩ :=
    WilliamsonShmoys.planar_drawing_face_data_for_edge_bound_1f6216d4 H hdraw hconn hV
  exact WilliamsonShmoys.face_count_edge_bound_1f6216d4 H F degree heuler hsum hdegree