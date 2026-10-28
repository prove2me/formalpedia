-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_extremal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:25:25.170554+00:00
-- url     : https://prove2.me/submissions/c404374e-1e78-4703-8227-9a5cc754f898
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hMax : forall Z : SimpleGraph V,
      HasPlanarDrawingOn Z ->
      (forall u v, Y.Adj u v -> Z.Adj u v) ->
      forall u v, Z.Adj u v -> Y.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
    Y hY hMax hCard
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
    Y hY hCard
  omega