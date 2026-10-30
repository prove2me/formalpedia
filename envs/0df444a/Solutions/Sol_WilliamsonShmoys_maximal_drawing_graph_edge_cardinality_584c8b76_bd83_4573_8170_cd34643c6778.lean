-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_graph_edge_cardinality_584c8b76_bd83_4573_8170_cd34643c6778
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:08:28.851976+00:00
-- url     : https://prove2.me/submissions/e96cc034-0967-4014-8eb5-cd42742b7320

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_drawing_graph_584c8b76
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_maximal_drawing_graph_584c8b76

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_graph_584c8b76 M hV hDraw
  · exact WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_graph_584c8b76 M hV hDraw hMax