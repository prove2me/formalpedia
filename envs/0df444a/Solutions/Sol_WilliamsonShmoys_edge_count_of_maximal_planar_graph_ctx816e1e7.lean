-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph_ctx816e1e7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:40:12.289409+00:00
-- url     : https://prove2.me/submissions/9d1e7436-afa9-4a44-b665-2c084c4a1c1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ctx816e1e7
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ctx816e1e7

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : forall S : SimpleGraph V, R <= S ->
      WilliamsonShmoys.HasPlanarDrawingOn S -> S <= R) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_upper_bound_ctx816e1e7 R hV hR
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7 R hV hR hmax
  omega
