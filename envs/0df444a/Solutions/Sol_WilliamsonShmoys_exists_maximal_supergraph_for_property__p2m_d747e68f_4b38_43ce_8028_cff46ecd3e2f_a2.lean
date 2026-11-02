-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_d747e68f_4b38_43ce_8028_cff46ecd3e2f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:05:48.717438+00:00
-- url     : https://prove2.me/submissions/4d6dc55d-caad-4ba7-9b9d-c91976d24d6c

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (L : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by
  classical
  let S : Set (SimpleGraph V) := {M | L ≤ M ∧ P M}
  have hS : S.Nonempty := ⟨L, le_rfl, hP⟩
  obtain ⟨M, hM⟩ := S.toFinite.exists_maximal hS
  refine ⟨M, hM.1.1, hM.1.2, ?_⟩
  intro N hMN hPN
  have hN : N ∈ S := ⟨hM.1.1.trans hMN, hPN⟩
  exact le_antisymm (hM.2 hN hMN) hMN