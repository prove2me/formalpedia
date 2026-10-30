-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_extension_b65312a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:42:30.870988+00:00
-- url     : https://prove2.me/submissions/1f0b8d3b-3785-4ea7-be97-913767644290

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_triangulated_extension_b65312a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_triangulated_extension_b65312a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNdraw, hNmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_triangulated_extension_b65312a2
      M hV hMdraw
  have hEdges :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulated_extension_b65312a2
      N hV hNdraw hNmax
  exact ⟨N, hMN, hNdraw, hEdges⟩