-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_inclusion_maximal_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:30:33.452929+00:00
-- url     : https://prove2.me/submissions/2c359166-0482-489c-b869-9a5feeae1e0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_face_count_certificate
import Theorems.Thm_WilliamsonShmoys_edge_count_from_euler_and_triangular_faces

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    L.edgeSet.ncard = 3 * n - 6 := by
  obtain ⟨f, hEuler, hTriangular⟩ :=
    WilliamsonShmoys.maximal_drawing_face_count_certificate
      L hDrawing hMax n hLarge hcard
  exact WilliamsonShmoys.edge_count_from_euler_and_triangular_faces
    n L.edgeSet.ncard f hLarge hEuler hTriangular