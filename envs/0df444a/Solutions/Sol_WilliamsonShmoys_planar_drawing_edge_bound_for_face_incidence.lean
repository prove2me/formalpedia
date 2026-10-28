-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_for_face_incidence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:18:51.758065+00:00
-- url     : https://prove2.me/submissions/a35b70ed-7da6-4b05-a879-400161bcad1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_face_certificate
import Theorems.Thm_WilliamsonShmoys_planar_face_certificate_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨faceCount, boundaryLength, hEuler, hIncidence, hBoundary⟩ :=
    WilliamsonShmoys.planar_drawing_has_face_certificate K hK hconn hV
  exact WilliamsonShmoys.planar_face_certificate_edge_bound K faceCount
    boundaryLength hEuler hIncidence hBoundary
