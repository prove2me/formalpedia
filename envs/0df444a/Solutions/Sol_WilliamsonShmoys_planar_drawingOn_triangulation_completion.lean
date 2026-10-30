-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:26:23.161783+00:00
-- url     : https://prove2.me/submissions/367e1886-741e-44ee-a33d-71895605f273

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_completion_55e40668_6c6c_445f_853d_a7074df51c4e
set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_completion_55e40668_6c6c_445f_853d_a7074df51c4e L hL hmax hV