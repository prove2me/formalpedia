-- Prove2me | solution 2 for WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph_of_three_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:26:10.605889+00:00
-- url     : https://prove2.me/submissions/0506df43-3431-44c4-a558-ad85f4e9c944
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_connected_closure_of_merge_with_card_bound
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_one_step_merge_with_card_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.finite_graph_property_connected_closure_of_merge_with_card_bound
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (fun K hKcard hK hKDisconnected =>
      WilliamsonShmoys.planar_disconnected_one_step_merge_with_card_bound
        K hKcard hK hKDisconnected)
    G hV hG hDisconnected