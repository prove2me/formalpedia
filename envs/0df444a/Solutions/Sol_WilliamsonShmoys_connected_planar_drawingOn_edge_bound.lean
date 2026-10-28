-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawingOn_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:29:47.956585+00:00
-- url     : https://prove2.me/submissions/a75192d0-e316-4566-b70d-fd8395186b53
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_face_census
import Theorems.Thm_WilliamsonShmoys_face_census_edge_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, degree, hEuler, hDegreeSum, hFaceDegree⟩ :=
    WilliamsonShmoys.planar_drawingOn_face_census K hK hconn hV
  exact WilliamsonShmoys.face_census_edge_bound
    (Fintype.card V) K.edgeSet.ncard f degree hV hEuler hDegreeSum hFaceDegree