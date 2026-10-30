-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulation_completion_with_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:48:00.237989+00:00
-- url     : https://prove2.me/submissions/a66d4ca2-cc83-456f-a98b-e3578134a831

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_completion_maximal_planar_drawing_4f89c2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edges_4f89c2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q.edgeSet ⊆ R.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hR, hmax⟩ :=
    WilliamsonShmoys.exists_completion_maximal_planar_drawing_4f89c2 Q hQ hV
  exact ⟨R, hQR, hR,
    WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2 R hV hR hmax⟩