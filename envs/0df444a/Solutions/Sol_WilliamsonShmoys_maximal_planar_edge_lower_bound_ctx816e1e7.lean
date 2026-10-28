-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_ctx816e1e7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:52:08.2356+00:00
-- url     : https://prove2.me/submissions/46d735ec-c422-42b2-8067-79b992e47766
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph_ctx816e1e7

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : forall S : SimpleGraph V, R <= S ->
      WilliamsonShmoys.HasPlanarDrawingOn S -> S <= R) :
    3 * Fintype.card V <= R.edgeSet.ncard + 6 := by
  have hex :=
    WilliamsonShmoys.planar_drawing_dense_supergraph_ctx816e1e7 R hV hR
  cases hex with
  | intro S hSExists =>
      cases hSExists with
      | intro hRS hRest =>
          cases hRest with
          | intro hS hbound =>
              have hSR : S <= R := hmax S hRS hS
              have hEq : S = R := le_antisymm hSR hRS
              cases hEq
              exact hbound
