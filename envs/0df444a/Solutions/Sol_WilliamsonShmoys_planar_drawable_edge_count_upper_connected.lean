-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_count_upper_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:19:50.49583+00:00
-- url     : https://prove2.me/submissions/743254d6-4145-4fd3-9e4c-5d148860efba

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_certificate
import Theorems.Thm_WilliamsonShmoys_face_certificate_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hconn : K.Connected) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨m, degree, heuler, hincidence, hdegree⟩ :=
    WilliamsonShmoys.planar_drawing_face_certificate K hV hK hconn
  exact WilliamsonShmoys.face_certificate_edge_bound K hV m degree heuler hincidence hdegree