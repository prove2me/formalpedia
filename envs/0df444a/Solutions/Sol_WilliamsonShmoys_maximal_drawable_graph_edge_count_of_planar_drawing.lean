-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_of_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:05:07.314987+00:00
-- url     : https://prove2.me/submissions/7d4c3407-78cc-4871-b7b1-a092a1e8c516
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_le
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_ge

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q -> Q = P)
    (hV : 3 <= Fintype.card V) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_simple_graph_edge_count_le P hdraw hV
  · exact WilliamsonShmoys.maximal_drawable_graph_edge_count_ge P hdraw hmax hV