-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:28:37.929607+00:00
-- url     : https://prove2.me/submissions/f4291be9-8c29-4aa0-9da2-b65429bed402

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_face_equations_finite_maximal_extension
import Theorems.Thm_WilliamsonShmoys_face_equations_edge_count_of_maximal_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDraw, hMax⟩ :=
    WilliamsonShmoys.face_equations_finite_maximal_extension M hDraw
  exact ⟨N, hMN, hNDraw,
    WilliamsonShmoys.face_equations_edge_count_of_maximal_drawing N hNDraw hMax hV⟩