-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:15:26.380043+00:00
-- url     : https://prove2.me/submissions/067f5d8d-2b68-4cc9-be5e-c5fcb14bfcea

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_triangulated_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count_for_triangulated_extension

open WilliamsonShmoys

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDrawing, hMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_for_triangulated_extension K hDrawing
  exact ⟨L, hKL, hLDrawing,
    WilliamsonShmoys.maximal_planar_extension_edge_count_for_triangulated_extension
      L hLDrawing hV hMaximal⟩