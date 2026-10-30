-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_property__p2m_e2b131f7_3fa6_4028_b77b_f247189916b8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:00.720656+00:00
-- url     : https://prove2.me/submissions/c63a7867-327c-479b-abd9-ae6cadb7491c

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ P M ∧ ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ P H}
  have hS : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨M, hM⟩ := hS.exists_maximal hne
  have hMG : G ≤ M := hM.1.1
  have hMP : P M := hM.1.2
  refine ⟨M, hMG, hMP, ?_⟩
  intro N hMN hPN
  have hNM : N ∈ S := ⟨le_trans hMG hMN, hPN⟩
  exact hM.2 hNM hMN