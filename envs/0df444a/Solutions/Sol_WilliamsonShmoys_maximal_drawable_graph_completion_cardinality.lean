-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_completion_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:51:34.875577+00:00
-- url     : https://prove2.me/submissions/1c5ac788-c573-42cf-a483-46ed38c79530

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_completion_cardinality_maximal_exists
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_completion_cardinality_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨W, hZW, hW, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_exists
      Z hV hZ
  exact ⟨W, hZW, hW,
    WilliamsonShmoys.maximal_drawable_graph_completion_cardinality_maximal_edge_count
      W hV hW hmax⟩