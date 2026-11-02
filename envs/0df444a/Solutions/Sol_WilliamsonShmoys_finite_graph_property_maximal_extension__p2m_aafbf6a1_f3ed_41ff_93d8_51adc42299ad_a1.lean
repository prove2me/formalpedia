-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_aafbf6a1_f3ed_41ff_93d8_51adc42299ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:28.031771+00:00
-- url     : https://prove2.me/submissions/c9a9e7ab-546b-4d29-87c0-38db9fac9cff

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ P M ∧ ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by
  classical
  let Q : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  have hQ : Q G := ⟨le_rfl, hG⟩
  obtain ⟨M, hGM, hM⟩ := (Set.toFinite {H : SimpleGraph V | Q H}).exists_le_maximal hQ
  refine ⟨M, hGM, hM.1.2, ?_⟩
  intro N hMN hPN
  have hNM : N ≤ M := hM.2 ⟨hGM.trans hMN, hPN⟩ hMN
  exact le_antisymm hNM hMN