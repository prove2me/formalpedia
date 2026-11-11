-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_qualifying_supergraph__p2m_7b028f0e_9557_4d63_b320_a3debd61f7f1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:54.265208+00:00
-- url     : https://prove2.me/submissions/6f394828-cbe2-4944-841b-6052f865e8d6

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_bounded_score_max__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ H' : SimpleGraph V, G ≤ H' → P H' → ¬ H < H' := by
  classical
  let score : SimpleGraph V → Nat := fun H =>
    Fintype.card {p : V × V // H.Adj p.1 p.2}
  let qualifies : SimpleGraph V → Prop := fun H => G ≤ H ∧ P H
  have hne : ∃ H, qualifies H := ⟨G, le_rfl, hP⟩
  obtain ⟨H, hH, hmax⟩ :=
    WilliamsonShmoys.exists_bounded_score_max__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
      qualifies score (Fintype.card (V × V))
      (by
        intro K hK
        exact
          (WilliamsonShmoys.simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1 K K).1 K)
      hne
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro H' hGH' hPH' hlt
  have hltScore :=
    (WilliamsonShmoys.simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1 H H').2 hlt
  have hmaxScore := hmax H' ⟨hGH', hPH'⟩
  exact (Nat.not_lt_of_ge hmaxScore) hltScore