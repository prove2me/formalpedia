-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:37:18.605519+00:00
-- url     : https://prove2.me/submissions/f5b340f2-2326-4377-b9a3-421e67144c3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bounds
import Theorems.Thm_WilliamsonShmoys_face_certificate_of_edge_bounds

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ (m : Nat) (degree : Fin m → ℤ),
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + m = 2 ∧
      (∑ f : Fin m, degree f) = 2 * (K.edgeSet.ncard : ℤ) ∧
      (∀ f, 3 <= degree f) := by
  obtain ⟨hLower, hUpper⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bounds K hV hK hconn
  exact WilliamsonShmoys.face_certificate_of_edge_bounds K hV hLower hUpper