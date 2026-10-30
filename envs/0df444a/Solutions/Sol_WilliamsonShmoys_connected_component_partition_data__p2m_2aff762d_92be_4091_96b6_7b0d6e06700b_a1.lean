-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:02.352667+00:00
-- url     : https://prove2.me/submissions/fccaad8b-5384-4c67-817b-fd28c1ec342d

import Theorems.Thm_WilliamsonShmoys_connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
import Theorems.Thm_WilliamsonShmoys_partition_edge_count_additive__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
import Theorems.Thm_WilliamsonShmoys_small_induced_simple_graph_edge_bound__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) ∧
      Fintype.card V = ∑ W ∈ parts, W.card ∧
      M.edgeSet.ncard = ∑ W ∈ parts, (M.induce (W : Set V)).edgeSet.ncard ∧
      (∀ W ∈ parts, (M.induce (W : Set V)).Connected) ∧
      (∀ W ∈ parts, W.card < 3 →
        (M.induce (W : Set V)).edgeSet.ncard ≤ W.card - 1) := by
  obtain ⟨parts, huniq, hcard, hconn, hclosed⟩ :=
    WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1 M
  have hedge := WilliamsonShmoys.partition_edge_count_additive__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1 M parts huniq hclosed
  refine ⟨parts, huniq, hcard, hedge, hconn, ?_⟩
  intro W hW hsmall
  exact WilliamsonShmoys.small_induced_simple_graph_edge_bound__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1 M W hsmall
