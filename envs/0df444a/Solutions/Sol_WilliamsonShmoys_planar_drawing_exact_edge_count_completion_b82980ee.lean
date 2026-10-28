-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion_b82980ee
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:58:39.426693+00:00
-- url     : https://prove2.me/submissions/842e21b3-5108-4769-bcfa-e22be7b786f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_for_exact_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_via_triangulation

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exact_count H hDraw
  exact ⟨K, hHK, hKDraw,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_via_triangulation
      K hCard hKDraw hMax⟩