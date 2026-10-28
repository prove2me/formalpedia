-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_connected_induced_components
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:38:31.095065+00:00
-- url     : https://prove2.me/submissions/80465f7b-bc37-4eaf-9df5-e977e233e756

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_edge_and_card_sums
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_finite_component_partition

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ (W : Set V) [Fintype W],
      3 ≤ Fintype.card W →
      (K.induce W).Connected →
      (K.induce W).edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨comps, hne, _hdisj, _hcover, hconnected, hcard, hedge⟩ :=
    WilliamsonShmoys.connected_component_partition_edge_and_card_sums K
  exact WilliamsonShmoys.planar_edge_bound_from_finite_component_partition
    K hV comps hne hconnected hcard hedge hconn