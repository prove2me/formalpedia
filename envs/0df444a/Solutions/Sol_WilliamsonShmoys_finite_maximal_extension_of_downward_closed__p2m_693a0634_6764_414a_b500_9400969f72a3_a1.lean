-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:26:21.50268+00:00
-- url     : https://prove2.me/submissions/c8948bb7-3c0a-4bd0-8d98-879dbfe15e9a

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hPN : P N)
    (hDown : ∀ G H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet → P H → P G) :
    ∃ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet ∧ P Q ∧
      ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → P R →
        R.edgeSet = Q.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun Q => P Q ∧ N ≤ Q
  have hpN : p N := ⟨hPN, le_rfl⟩
  obtain ⟨Q, _hNQ, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hmax with ⟨hpQ, hmax'⟩
  have hsub : N.edgeSet ⊆ Q.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hpQ.2
  refine ⟨Q, hsub, hpQ.1, ?_⟩
  intro R hQR hPR
  have hQRle : Q ≤ R := SimpleGraph.edgeSet_subset_edgeSet.mp hQR
  have hpR : p R := ⟨hPR, hpQ.2.trans hQRle⟩
  have hRQle : R ≤ Q := hmax' hpR hQRle
  exact le_antisymm (SimpleGraph.edgeSet_subset_edgeSet.mpr hRQle) hQR
