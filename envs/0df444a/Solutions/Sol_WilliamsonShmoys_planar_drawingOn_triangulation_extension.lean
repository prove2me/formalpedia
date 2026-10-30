-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:07:55.627858+00:00
-- url     : https://prove2.me/submissions/0b4c612a-de46-47dc-9627-521fdd70de99

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hMK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_exists_maximal_extension M hM
  refine ⟨K, hMK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawingOn_edge_count K hV hK hmax