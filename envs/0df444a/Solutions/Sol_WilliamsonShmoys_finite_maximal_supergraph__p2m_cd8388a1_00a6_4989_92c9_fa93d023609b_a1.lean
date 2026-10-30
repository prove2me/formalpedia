-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph__p2m_cd8388a1_00a6_4989_92c9_fa93d023609b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:08.177659+00:00
-- url     : https://prove2.me/submissions/461c25bf-0862-4506-99d3-4267e9599bf9

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_edge_card_max_graph_family__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_strict_of_lt__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by
  classical
  obtain ⟨M, hM, hmax⟩ :=
    WilliamsonShmoys.exists_edge_card_max_graph_family__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
      (fun H => G ≤ H ∧ P H) ⟨G, le_rfl, hP⟩
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hPN
  by_contra hneq
  have hMNne : M ≠ N := fun heq => hneq heq.symm
  have hlt := WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
    M N hMN hMNne
  exact (not_lt_of_ge (hmax N ⟨le_trans hM.1 hMN, hPN⟩)) hlt