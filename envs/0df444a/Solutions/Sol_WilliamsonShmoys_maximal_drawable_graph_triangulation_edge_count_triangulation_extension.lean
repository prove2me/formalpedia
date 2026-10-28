-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:00:57.994992+00:00
-- url     : https://prove2.me/submissions/4bf2cccd-72d6-47ce-ab5b-8e3d2e2bc46d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_maximal_drawable_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, K ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hKT, hT, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_exists_maximal_drawable_extension K hK
  exact ⟨T, hKT, hT,
    WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_maximal_drawable_edge_count
      T hT hV hmax⟩