-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph_same_vertex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:51:42.860507+00:00
-- url     : https://prove2.me/submissions/5a7c27da-a291-4318-8c72-cbb7076cb3a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_maximal_supergraph_same_vertex
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_of_arcs

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMdraw, hMax⟩ :=
    WilliamsonShmoys.exists_drawable_edge_maximal_supergraph_same_vertex L hDrawing
  exact ⟨M, hLM, hMdraw,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_of_arcs M hMdraw hCard hMax⟩