-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:46:24.788279+00:00
-- url     : https://prove2.me/submissions/b7624f1f-58e3-40bb-b8a5-e0aae4a9da65

import Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_subgraph_closed

import Mathlib

theorem solution {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∀ K : SimpleGraph V, H ≤ K → P K → K = H :=
  WilliamsonShmoys.exists_maximal_of_finite_subgraph_closed P hdown G hG
