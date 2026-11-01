-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_236ff196_eb97_4260_bf50_22869620a85a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:51.449315+00:00
-- url     : https://prove2.me/submissions/0b70199d-156f-4c18-bda2-4708e4016f75

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ L : SimpleGraph V,
      P L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      (∀ M : SimpleGraph V,
        P M →
        (∀ u v, L.Adj u v → M.Adj u v) →
        ∀ u v, M.Adj u v → L.Adj u v) := by
  classical
  obtain ⟨L, hdec, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      (fun G : SimpleGraph V => P G ∧ K ≤ G)).2
      ⟨K, hK, le_rfl⟩
  letI := hdec
  refine ⟨L, hmax.1.1, hmax.1.2, ?_⟩
  intro M hPM hLM
  have hqM : P M ∧ K ≤ M := ⟨hPM, hmax.1.2.trans hLM⟩
  have heq : L = M := (hmax.le_iff_eq hqM).mp hLM
  have hML : M ≤ L := le_of_eq heq.symm
  exact fun u v huv => hML huv