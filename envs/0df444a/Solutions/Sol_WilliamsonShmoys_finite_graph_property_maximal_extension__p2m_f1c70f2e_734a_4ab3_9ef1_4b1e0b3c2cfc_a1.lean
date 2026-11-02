-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_f1c70f2e_734a_4ab3_9ef1_4b1e0b3c2cfc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:50:05.891205+00:00
-- url     : https://prove2.me/submissions/23b49980-606e-4a7e-889d-e5aef9ea788b

import Mathlib
import Theorems.Thm_finite_set_has_maximal_simplegraph_extension__p2m_3dd2f00a_a125_4333_88d9_0f94f3546b41_a2

open SimpleGraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ P K}
  have hSf : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hKS, hmax⟩ :=
    finite_set_has_maximal_simplegraph_extension__p2m_3dd2f00a_a125_4333_88d9_0f94f3546b41_a2
      S hSf hSne
  refine ⟨K, hKS.1, hKS.2, ?_⟩
  intro L hKL hPL
  have hLS : L ∈ S := ⟨le_trans hKS.1 hKL, hPL⟩
  have hLK := hmax L hLS hKL
  exact (le_antisymm hKL hLK).symm
