-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_repair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:39:38.793629+00:00
-- url     : https://prove2.me/submissions/13aa71aa-0a14-48c5-86a4-bb69ff23fa22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.maximal_drawable_graph_edge_count_upper T hV hT
  have hlower := WilliamsonShmoys.maximal_drawable_graph_edge_count_lower T hV hT hmax
  omega