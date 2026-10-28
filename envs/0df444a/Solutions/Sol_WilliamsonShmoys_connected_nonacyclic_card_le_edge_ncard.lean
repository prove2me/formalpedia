-- Prove2me | solution 1 for WilliamsonShmoys.connected_nonacyclic_card_le_edge_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:41:32.023263+00:00
-- url     : https://prove2.me/submissions/4213651a-821d-4bc3-9c31-6619dd387452

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hCyclic : ¬ G.IsAcyclic) :
    Fintype.card V ≤ G.edgeSet.ncard := by
  classical
  have hbound := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hConnected
  have hbound' : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using hbound
  by_contra h
  have hlt : G.edgeSet.ncard < Fintype.card V := Nat.lt_of_not_ge h
  have heq : G.edgeSet.ncard + 1 = Fintype.card V := by omega
  have htree : G.IsTree := by
    apply (SimpleGraph.isTree_iff_connected_and_card).2
    exact ⟨hConnected, by
      simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using heq⟩
  exact hCyclic htree.isAcyclic