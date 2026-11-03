-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_simpleGraph__p2m_629021cc_ee60_4d9a_a83c_dbd077e630a9_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:29:51.743434+00:00
-- url     : https://prove2.me/submissions/f8d5627b-ce00-4014-bb7d-f05832bc3bd1

import Theorems.Thm_WilliamsonShmoys_exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H :=
  WilliamsonShmoys.exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1 P G hG