-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:59:08.628221+00:00
-- url     : https://prove2.me/submissions/4ce619c4-6483-417e-a09f-1b334460d9f0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_face_count_data
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_from_face_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data
      K hV hK hconn
  exact WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_from_face_count
    (Fintype.card V) K.edgeSet.ncard f hV hEuler hFaces