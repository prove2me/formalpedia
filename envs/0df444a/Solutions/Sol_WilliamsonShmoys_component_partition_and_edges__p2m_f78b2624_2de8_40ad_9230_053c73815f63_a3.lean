-- Prove2me | solution 1 for WilliamsonShmoys.component_partition_and_edges__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:27:42.632789+00:00
-- url     : https://prove2.me/submissions/49f78bd2-f42b-4b70-8cca-443d11b1449d

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_partition_connected_components__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
import Theorems.Thm_WilliamsonShmoys_component_partition_edge_card_sum__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj) :
    ∃ C : Finset (Finset V),
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s) ∧
      (∀ s ∈ C, (N.induce (s : Set V)).Connected) ∧
      N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card := by
  obtain ⟨C, hnonempty, hpartition, hconnected, hadj_closed⟩ :=
    WilliamsonShmoys.component_partition_connected_components__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
      N dN
  have hedge_count :=
    WilliamsonShmoys.component_partition_edge_card_sum__p2m_e69e75b7_a85c_4c30_aae7_c16779d08e89_a1
      N dN C hpartition hadj_closed
  exact ⟨C, hnonempty, hpartition, hconnected, hedge_count⟩