-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_triangulation_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:02:55.871987+00:00
-- url     : https://prove2.me/submissions/b11deea7-8499-4118-8c0e-30ebbb7e1142

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_maximal_drawable_supergraph
import Theorems.Thm_WilliamsonShmoys_triangulation_maximal_drawable_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.triangulation_maximal_drawable_supergraph K hV hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.triangulation_maximal_drawable_edge_count L hV hL hmax