-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_finite_component_partition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:11:22.155732+00:00
-- url     : https://prove2.me/submissions/89d0438a-699f-4811-ab63-a39a6ef6c63b

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_edge_bound
import Theorems.Thm_WilliamsonShmoys_sum_component_edge_bounds

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (comps : Finset (Set V))
    (hne : ∀ C ∈ comps, C.Nonempty)
    (hconnected : ∀ C ∈ comps, (K.induce C).Connected)
    (hcard : ∑ C ∈ comps, C.ncard = Fintype.card V)
    (hedge : K.edgeSet.ncard = ∑ C ∈ comps, (K.induce C).edgeSet.ncard)
    (hconn : ∀ (W : Set V) [Fintype W],
      3 ≤ Fintype.card W →
      (K.induce W).Connected →
      (K.induce W).edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  rw [hedge]
  exact WilliamsonShmoys.sum_component_edge_bounds K comps hne hV hcard (by
    intro C hC
    letI : Fintype C := Fintype.ofFinite C
    exact WilliamsonShmoys.connected_component_edge_bound K C
      (hne C hC) (hconnected C hC) hconn)