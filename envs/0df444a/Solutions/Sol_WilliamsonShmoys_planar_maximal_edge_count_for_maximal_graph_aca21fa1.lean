-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count_for_maximal_graph_aca21fa1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:24:03.284462+00:00
-- url     : https://prove2.me/submissions/1604d372-d336-48c8-9c49-5cb2e97eef07

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_aca21fa1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_aca21fa1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : HasPlanarDrawingOn Z)
    (hCard : 3 <= Fintype.card V)
    (hmax : (W : SimpleGraph V) -> HasPlanarDrawingOn W ->
      ((u v : V) -> Z.Adj u v -> W.Adj u v) ->
      (u v : V) -> W.Adj u v -> Z.Adj u v) :
    (Z.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_aca21fa1 Z hZ hCard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_aca21fa1 Z hZ hCard hmax
  omega