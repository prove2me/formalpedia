-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_predicate_maximal_extension__p2m_03e90475_cbaa_4d30_84cc_f87b4a621968_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:04:23.988998+00:00
-- url     : https://prove2.me/submissions/d9cb5007-ebfc-4d11-8bce-7036744d6e96

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  classical
  let Q : SimpleGraph V → Prop := fun G => K ≤ G ∧ P G
  obtain ⟨L, _, hL⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (V := V) Q).2
      ⟨K, le_rfl, hK⟩
  refine ⟨L, hL.1.1, hL.1.2, ?_⟩
  intro M hLM hPM
  have hEq : L = M :=
    (SimpleGraph.IsExtremal.le_iff_eq hL
      ⟨le_trans hL.1.1 hLM, hPM⟩).mp hLM
  exact le_of_eq hEq.symm