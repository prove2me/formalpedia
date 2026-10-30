-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_completion_with_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:00:27.8448+00:00
-- url     : https://prove2.me/submissions/2a473937-abc1-470c-811d-b143a3e445f0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_drawable_extension
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_has_triangulation_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_edge_maximal_drawable_extension H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.edge_maximal_drawable_graph_has_triangulation_edge_count
    K hK hmax hCard