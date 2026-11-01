-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_graph_extension_finite__p2m_8483dba4_46b0_4557_8588_2cfeb83216a6_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:25.863419+00:00
-- url     : https://prove2.me/submissions/0ef5ce1c-1c27-4ae5-91fb-2858973124bd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_exists_maximal_witness_finite__p2m_9f3e6a97_c623_4a15_9543_38a021dd3fb9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hH : P H) :
    Exists fun K : SimpleGraph V => H ≤ K ∧ P K ∧
      ∀ K' : SimpleGraph V, K ≤ K' → P K' → K' = K := by
  classical
  let Q : SimpleGraph V → Prop := fun K => H ≤ K ∧ P K
  have hQ : ∃ K, Q K := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hMax⟩ :=
    exists_maximal_witness_finite__p2m_9f3e6a97_c623_4a15_9543_38a021dd3fb9_a1 Q hQ
  exact ⟨K, hK.1, hK.2, fun K' hKK' hPK' =>
    hMax K' ⟨le_trans hK.1 hKK', hPK'⟩ hKK'⟩