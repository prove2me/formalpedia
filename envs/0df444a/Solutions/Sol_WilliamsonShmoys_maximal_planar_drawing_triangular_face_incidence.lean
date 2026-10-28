-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangular_face_incidence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:07:06.235968+00:00
-- url     : https://prove2.me/submissions/06466c0f-52e6-4e89-b73a-4580e87d1707
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_ad420e80

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet)
    (f : ℕ) (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    3 * f = 2 * H.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_drawing_edge_count_ad420e80
    H hCard hDraw hMax
  omega