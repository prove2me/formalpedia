-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_d1156ce4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:17:51.799904+00:00
-- url     : https://prove2.me/submissions/2a0725df-694a-4eb9-bc99-45c2954c3a32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_data
import Theorems.Thm_WilliamsonShmoys_triangulation_face_count_forces_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : forall J : SimpleGraph V, H <= J -> HasPlanarDrawingOn J -> J = H)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨F, instF, boundaryLength, hEuler, hIncidence, hTriangle⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_data H hDraw hMax hCard
  letI : Fintype F := instF
  exact WilliamsonShmoys.triangulation_face_count_forces_edge_count
    (n := Fintype.card V) (e := H.edgeSet.ncard) boundaryLength hEuler
    hIncidence hTriangle
