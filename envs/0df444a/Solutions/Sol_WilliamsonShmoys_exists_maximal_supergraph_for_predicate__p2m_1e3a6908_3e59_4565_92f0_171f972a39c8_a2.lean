-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_1e3a6908_3e59_4565_92f0_171f972a39c8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:25:50.160803+00:00
-- url     : https://prove2.me/submissions/c66e588e-b5d3-4388-9eef-a3148b182e29

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ K' : SimpleGraph V, K ≤ K' → P K' → K' = K := by
  classical
  let Q : SimpleGraph V → Prop := fun G => H ≤ G ∧ P G
  have hQ : ∃ G : SimpleGraph V, Q G := ⟨H, le_rfl, hH⟩
  obtain ⟨K, _, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 hQ
  refine ⟨K, hmax.1.1, hmax.1.2, ?_⟩
  intro K' hKK' hPK'
  have hQK' : Q K' := ⟨hmax.1.1.trans hKK', hPK'⟩
  exact ((hmax.le_iff_eq hQK').1 hKK').symm