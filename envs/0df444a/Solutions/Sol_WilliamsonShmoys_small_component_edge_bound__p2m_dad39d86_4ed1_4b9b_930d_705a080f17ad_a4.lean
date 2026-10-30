-- Prove2me | solution 1 for WilliamsonShmoys.small_component_edge_bound__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:27:50.583985+00:00
-- url     : https://prove2.me/submissions/ad061f2b-a37a-4bd6-8fd7-d1eb54069242

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (hsmall : C.supp.ncard < 3) :
    C.toSimpleGraph.edgeSet.ncard ≤ 1 := by
  classical
  have hcard : Fintype.card C ≤ 2 := by
    have h1 : Nat.card C = C.supp.ncard := by
      exact Nat.card_coe_set_eq _
    rw [Nat.card_eq_fintype_card] at h1
    omega
  have h2 : C.toSimpleGraph.edgeSet.ncard = (C.toSimpleGraph.edgeFinset).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr
  rw [h2]
  have h3 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := C.toSimpleGraph)
  have h4 : (Fintype.card C).choose 2 ≤ 1 := by
    interval_cases hc : Fintype.card C <;> simp
  omega
