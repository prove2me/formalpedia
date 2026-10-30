-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations_a76877fd_7551_4249_899d_5acc3f351e6a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:38:02.02599+00:00
-- url     : https://prove2.me/submissions/7de71a15-7dba-4ac9-adf4-303f62d0fbb9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_for_maximal_face_equations

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = N.edgeSet.ncard + 2 ∧
      3 * f = 2 * N.edgeSet.ncard := by
  obtain ⟨K, hNK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations
      N hDraw hV
  have hKN : K = N := hMax K hNK hKDraw
  subst K
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega