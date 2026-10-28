-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_f15616f1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:24:01.884489+00:00
-- url     : https://prove2.me/submissions/113b0931-77fd-49a9-84f0-8ed030b59dcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound_f15616f1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_f15616f1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    (∀ J : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn J →
      H ≤ J → H = J) →
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  intro hmax
  have hupper :=
    WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_f15616f1
      H hH hCard
  have hlower :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_f15616f1
      H hH hCard hmax
  omega