-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:48:59.084265+00:00
-- url     : https://prove2.me/submissions/7c58051c-d3b9-4923-84b3-e137a58c356a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_face_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangular_face_incidence

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    ∃ f : ℕ, 3 * f = 2 * H.edgeSet.ncard ∧
      Fintype.card V + f = H.edgeSet.ncard + 2 := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_euler_face_count
      H hCard hDraw hMax
  have hTri :=
    WilliamsonShmoys.maximal_planar_drawing_triangular_face_incidence
      H hCard hDraw hMax f hEuler
  exact ⟨f, hTri, hEuler⟩