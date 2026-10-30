-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_card_upper_bound_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:53:51.553462+00:00
-- url     : https://prove2.me/submissions/13430357-4483-4567-9ef2-a767192d9e38

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_edge_card

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hConnected : S.Connected) :
    S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hTPlanar, hEdges, hTCard⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_edge_card
      S hS hCard hConnected
  rw [← hTCard]
  exact hEdges