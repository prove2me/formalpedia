-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:25:07.846638+00:00
-- url     : https://prove2.me/submissions/dffe18a4-cbee-4478-8a44-d3ea4e3c29d1

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_edge_bound_from_hypothesis
import Theorems.Thm_WilliamsonShmoys_aggregate_connected_component_edge_bounds

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hS : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  apply WilliamsonShmoys.aggregate_connected_component_edge_bounds K hV
  intro C hC
  exact WilliamsonShmoys.connected_component_edge_bound_from_hypothesis K hS C hC