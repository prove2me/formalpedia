-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:36:47.869551+00:00
-- url     : https://prove2.me/submissions/92d2abe6-3b37-43eb-82e0-c5bee8b76a59
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_under_drawing_584c8b76_bd83_4573_8170_cd34643c6778
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_graph_edge_cardinality_584c8b76_bd83_4573_8170_cd34643c6778

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hDrawM, hMax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_under_drawing_584c8b76_bd83_4573_8170_cd34643c6778 L hDraw
  have hCount := WilliamsonShmoys.maximal_drawing_graph_edge_cardinality_584c8b76_bd83_4573_8170_cd34643c6778 M hV hDrawM hMax
  exact ⟨M, hLM, hDrawM, hCount⟩