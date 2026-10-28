-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_count_aggregation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:33:36.689969+00:00
-- url     : https://prove2.me/submissions/ca6b4895-249a-4c89-bf0e-70c246e90e58

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_partition_card_sum
import Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_induced_edge_count_sum
import Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_piecewise_sum_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S)
    (hLocal : ∀ S ∈ C,
      (H.induce (↑S : Set V)).edgeSet.ncard ≤
        (if S.card < 3 then S.card / 2 else 3 * S.card - 6))
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have hEdges :
      H.edgeSet.ncard =
        C.sum (fun S => (H.induce (↑S : Set V)).edgeSet.ncard) :=
    WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum
      V H C hPartition hNoCross
  have hCards : C.sum Finset.card = Fintype.card V :=
    WilliamsonShmoys.component_edge_count_aggregation_partition_card_sum
      V C hPartition
  rw [hEdges]
  exact WilliamsonShmoys.component_edge_count_aggregation_piecewise_sum_bound
    C (fun S => (H.induce (↑S : Set V)).edgeSet.ncard) hCards
    (by
      intro S hS
      exact hLocal S hS)
    hV