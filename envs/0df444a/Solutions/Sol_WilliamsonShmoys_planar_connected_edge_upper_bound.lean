-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:40:07.884504+00:00
-- url     : https://prove2.me/submissions/7d3e27c4-9cc4-4de4-a3f1-6cd80bc8f696
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_face_certificate
import Theorems.Thm_WilliamsonShmoys_face_certificate_to_edge_bound

set_option autoImplicit false

/-- Euler's edge bound follows from a finite face decomposition and the
minimum length of every face boundary. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hConnected : L.Connected)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨F, faceLength, hF, hEuler, hIncidences, hFaceLength⟩ :=
    WilliamsonShmoys.planarDrawingOn_face_certificate L hConnected hL hV
  exact WilliamsonShmoys.face_certificate_to_edge_bound
    L F faceLength hF hEuler hIncidences hFaceLength hV