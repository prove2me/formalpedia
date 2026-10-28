-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edge_count_supergraph__p2m_eef664be_1603_4195_b44b_d81e1ccffc6c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:22:26.614276+00:00
-- url     : https://prove2.me/submissions/548e5e31-ec36-4ab7-9739-7c22f86b3ff5

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (J : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hJ : P J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let α := {K : SimpleGraph V // J ≤ K ∧ P K}
  let s : Finset α := Finset.univ
  have hs : s.Nonempty := by
    refine ⟨⟨J, le_rfl, hJ⟩, ?_⟩
    simp [s]
  obtain ⟨k, hk, hmax⟩ :=
    Finset.exists_max_image s (fun k : α => k.1.edgeSet.ncard) hs
  refine ⟨k.1, k.2.1, k.2.2, ?_⟩
  intro L hKL hPL
  have hJL : J ≤ L := le_trans k.2.1 hKL
  have hL : (⟨L, hJL, hPL⟩ : α) ∈ s := by
    simp [s]
  exact hmax ⟨L, hJL, hPL⟩ hL