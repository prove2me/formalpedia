-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_euler_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:30:25.328989+00:00
-- url     : https://prove2.me/submissions/cd32e1fc-fb01-4181-8a1d-3b72f75cc889

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_for_face_inequalities
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_face_inequalities

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f <= 2 * K.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_count_for_face_inequalities K hconn hdraw
  have hedge :=
    WilliamsonShmoys.planar_drawing_edge_bound_for_face_inequalities K hconn hdraw hV
  refine ⟨f, heuler, ?_⟩
  nlinarith