-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:54.454318+00:00
-- url     : https://prove2.me/submissions/dec01ff7-944b-4eef-9aeb-72a6c2c32f8c

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1
import Theorems.Thm_finite_partition_card_sum__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ v : V, ∃! W : Finset V, W ∈ parts ∧ v ∈ W) ∧
      Fintype.card V = ∑ W ∈ parts, W.card ∧
      (∀ W ∈ parts, (M.induce (W : Set V)).Connected) ∧
      (∀ u v : V, M.Adj u v → ∃ W ∈ parts, u ∈ W ∧ v ∈ W) := by
  obtain ⟨parts, hpartition, hconnected, hedge⟩ :=
    WilliamsonShmoys.connected_component_partition_family__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1 M
  have hcard := finite_partition_card_sum__p2m_94e5824a_c757_4689_bf4f_99cc2f2adc56_a1 parts hpartition
  exact ⟨parts, hpartition, hcard, hconnected, hedge⟩