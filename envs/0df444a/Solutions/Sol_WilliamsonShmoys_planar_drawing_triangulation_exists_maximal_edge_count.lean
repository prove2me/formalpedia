-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_exists_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:53:58.411137+00:00
-- url     : https://prove2.me/submissions/3efde9b2-754c-44ba-b3e9-30d1d8f37fe5

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_face_count_equations
import Theorems.Thm_WilliamsonShmoys_face_count_equations_edge_formula

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_face_count_equations
      L hV hLplanar hmax
  exact WilliamsonShmoys.face_count_equations_edge_formula
    (L := L) f hEuler hIncidence