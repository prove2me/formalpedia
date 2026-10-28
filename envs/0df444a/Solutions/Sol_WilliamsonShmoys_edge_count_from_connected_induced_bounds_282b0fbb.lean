-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_from_connected_induced_bounds_282b0fbb
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:57:49.9187+00:00
-- url     : https://prove2.me/submissions/cb9bff11-03eb-4e1a-8ecc-3d34e910cb42

import Theorems.Thm_WilliamsonShmoys_edge_count_aggregate_components
import Theorems.Thm_WilliamsonShmoys_connected_component_sums
import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hConnectedBounds :
      ∀ S : Finset V, 3 <= S.card → (L.induce S).Connected →
        ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨C, hCardSum, hEdgeSum, hConnected⟩ :=
    WilliamsonShmoys.connected_component_sums L
  exact WilliamsonShmoys.edge_count_aggregate_components
    L C hCard hConnectedBounds hCardSum hEdgeSum hConnected
