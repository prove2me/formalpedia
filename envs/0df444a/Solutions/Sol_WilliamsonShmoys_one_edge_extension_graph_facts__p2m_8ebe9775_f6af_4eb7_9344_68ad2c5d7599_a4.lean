-- Prove2me | solution 1 for WilliamsonShmoys.one_edge_extension_graph_facts__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T14:58:47.713013+00:00
-- url     : https://prove2.me/submissions/adbf587b-a05b-406d-906f-8dd05ef706f6

import Mathlib

set_option autoImplicit false

/-- A single added edge strictly increases the edge count, and the original graph is a subgraph. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (u v : V) (huv : u ≠ v) (hUnreachable : ¬ N.Reachable u v) :
    let K : SimpleGraph V :=
      N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)
    N ≤ K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card < K.edgeFinset.card) := by
  classical
  dsimp only
  constructor
  · exact le_sup_left
  · have hsub : N.edgeSet ⊆
        (N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)).edgeSet :=
      SimpleGraph.edgeSet_mono le_sup_left
    have hmem : s(u, v) ∈
        (N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)).edgeSet := by
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.fromRel_adj]
      exact ⟨huv, Or.inl ⟨rfl, rfl⟩⟩
    have hnot : s(u, v) ∉ N.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      intro h
      exact hUnreachable h.reachable
    have hproper : N.edgeSet ⊂
        (N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)).edgeSet := by
      rw [Set.ssubset_iff_of_subset hsub]
      exact ⟨s(u, v), hmem, hnot⟩
    have hlt : N.edgeSet.ncard <
        (N ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)).edgeSet.ncard :=
      Set.ncard_lt_ncard hproper (Set.toFinite _)
    rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card,
      Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact hlt
