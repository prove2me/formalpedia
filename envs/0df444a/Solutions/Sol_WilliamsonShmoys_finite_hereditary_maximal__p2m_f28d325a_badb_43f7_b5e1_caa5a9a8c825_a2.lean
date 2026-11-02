-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_maximal__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:48:24.713387+00:00
-- url     : https://prove2.me/submissions/aa1d840f-9b3f-452b-b2ad-7877d720883d

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hG : P G)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
        ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  classical
  let Q : SimpleGraph V → Prop := fun K => G ≤ K ∧ P K
  obtain ⟨H, hDec, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2
      ⟨G, ⟨le_rfl, hG⟩⟩
  refine ⟨H, hmax.1.1, hmax.1.2, ?_⟩
  intro K hHK hPK
  have hQK : Q K := ⟨hmax.1.1.trans hHK, hPK⟩
  have hEq : H = K :=
    (SimpleGraph.IsExtremal.le_iff_eq hmax hQK).mp hHK
  exact hEq.symm