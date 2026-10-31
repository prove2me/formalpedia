-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph__p2m_3d3a53f5_6da9_483c_b0e6_94f0720675a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:42:58.998164+00:00
-- url     : https://prove2.me/submissions/6c05c9b8-130d-4f62-ade0-dd0d3bbc0479

import Theorems.Thm_WilliamsonShmoys_finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ (∀ K : SimpleGraph V, H ≤ K → P K → K ≤ H) :=
  WilliamsonShmoys.finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1 P G hG
