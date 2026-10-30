-- Prove2me | solution 1 for WilliamsonShmoys.finite_subgraph_closed_maximal__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:44.375709+00:00
-- url     : https://prove2.me/submissions/f0dd51fc-3552-478b-9299-8fd22138a561

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_poset_nonempty_subset_has_maximal__p2m_f1350172_eccd_4d30_8af3_b1246339198a_a1

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hsub : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  classical
  let Q : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  have hQ : ∃ G : SimpleGraph V, Q G := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hLQ, hLmax⟩ :=
    WilliamsonShmoys.finite_poset_nonempty_subset_has_maximal__p2m_f1350172_eccd_4d30_8af3_b1246339198a_a1
      (α := SimpleGraph V) Q hQ
  refine ⟨L, hLQ.1, hLQ.2, ?_⟩
  intro M hLM hPM
  have hQM : Q M := ⟨le_trans hLQ.1 hLM, hPM⟩
  exact hLmax M hLM hQM