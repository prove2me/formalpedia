-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_e07f1b1a_1ea6_4563_8b26_8f130e22d586_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:04:38.764553+00:00
-- url     : https://prove2.me/submissions/f7793011-23f0-47c8-9584-d3c28136fe49

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V)
    (hH : P H) (B : Nat)
    (hbound : ∀ G : SimpleGraph V, P G → G.edgeSet.ncard ≤ B) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  let S : SimpleGraph V → Prop := fun G => H ≤ G ∧ P G
  obtain ⟨K, hHK, hKmax⟩ :=
    Finite.exists_le_maximal (p := S) (a := H) ⟨le_rfl, hH⟩
  refine ⟨K, hHK, hKmax.1.2, ?_⟩
  intro L hKL hPL
  have hL : S L := ⟨hHK.trans hKL, hPL⟩
  exact hKmax.2 hL hKL
