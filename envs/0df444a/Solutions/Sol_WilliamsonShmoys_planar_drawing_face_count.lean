-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:41:17.015786+00:00
-- url     : https://prove2.me/submissions/b3de5565-8362-4a7b-91cf-91ad05707be6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      K.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  obtain ⟨f, hf⟩ := WilliamsonShmoys.planar_drawing_euler K hK hconn
  exact ⟨f, hf, WilliamsonShmoys.planar_drawing_face_incidence K hK hconn hV f hf⟩
