-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_face_lengths
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:44:29.555152+00:00
-- url     : https://prove2.me/submissions/20544c5f-1c2b-4871-8f5c-a8da9e016443
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (heuler : Fintype.card V + f = K.edgeSet.ncard + 2) :
    ∃ degree : Fin f → ℕ,
      (∑ i : Fin f, degree i) = 2 * K.edgeSet.ncard ∧
      ∀ i, 3 ≤ degree i := by
  obtain ⟨m, hfaces, degree, hsum, hdegree⟩ :=
    WilliamsonShmoys.planar_drawing_face_data K hK hconn hV
  have hm : m = f := by omega
  subst m
  exact ⟨degree, hsum, hdegree⟩