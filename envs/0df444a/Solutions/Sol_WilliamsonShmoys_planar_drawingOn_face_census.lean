-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_face_census
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:39:49.522522+00:00
-- url     : https://prove2.me/submissions/eef79b0f-b110-4a5f-a599-f3b8ce470f7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_euler
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_face_lengths

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, ∃ degree : Fin f → ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      (∑ i : Fin f, degree i) = 2 * K.edgeSet.ncard ∧
      ∀ i, 3 ≤ degree i := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawingOn_euler K hK hconn
  obtain ⟨degree, hsum, hdegree⟩ :=
    WilliamsonShmoys.planar_drawingOn_face_lengths K hK hconn hV f heuler
  exact ⟨f, degree, heuler, hsum, hdegree⟩