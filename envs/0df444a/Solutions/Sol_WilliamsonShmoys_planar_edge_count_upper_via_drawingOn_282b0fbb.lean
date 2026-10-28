-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_via_drawingOn_282b0fbb
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:31:52.909501+00:00
-- url     : https://prove2.me/submissions/c366c032-f9e4-49d5-adb5-2f92b11981e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected_drawingOn_282b0fbb
import Theorems.Thm_WilliamsonShmoys_drawingOn_restrict_induce_282b0fbb
import Theorems.Thm_WilliamsonShmoys_edge_count_from_connected_induced_bounds_282b0fbb

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  have hConnectedBounds :
      ∀ S : Finset V, 3 <= S.card → (L.induce S).Connected →
        ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6 := by
    intro S hS hConnected
    have hSubtypeCard : 3 <= Fintype.card ↥S := by
      simpa using hS
    have hBound := WilliamsonShmoys.planar_edge_count_connected_drawingOn_282b0fbb
      (L.induce S)
      (WilliamsonShmoys.drawingOn_restrict_induce_282b0fbb L hL S)
      hSubtypeCard
      hConnected
    simpa using hBound
  exact WilliamsonShmoys.edge_count_from_connected_induced_bounds_282b0fbb
    L hCard hConnectedBounds
