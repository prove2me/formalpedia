-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_card_upper_bound_f3620a14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:27:13.925183+00:00
-- url     : https://prove2.me/submissions/74ec0604-2ff3-43ad-840a-5d28f8a82e62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_upper_bound_disconnected

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  by_cases hConnected : S.Connected
  · exact WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected
      S hS hCard hConnected
  · exact WilliamsonShmoys.planar_drawing_edge_card_upper_bound_disconnected
      S hS hCard hConnected