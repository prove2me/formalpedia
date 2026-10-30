-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_face_equations_e944d3e8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:26:36.196463+00:00
-- url     : https://prove2.me/submissions/5de6b8ca-fc3b-47f6-be68-636e8c3782c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_face_equations_planar_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_face_equations_maximal_planar_edge_count_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.face_equations_planar_edge_count_upper_bound M hDraw hV
  have hLower := WilliamsonShmoys.face_equations_maximal_planar_edge_count_lower_bound M hDraw hMax hV
  omega