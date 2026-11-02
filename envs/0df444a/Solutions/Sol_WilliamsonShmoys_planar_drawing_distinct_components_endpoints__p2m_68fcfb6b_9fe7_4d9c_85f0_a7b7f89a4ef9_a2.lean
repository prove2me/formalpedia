-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_distinct_components_endpoints__p2m_68fcfb6b_9fe7_4d9c_85f0_a7b7f89a4ef9_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:13.108812+00:00
-- url     : https://prove2.me/submissions/b65f6876-fe8c-4b7b-8183-53afc7c829b6

import Mathlib

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V), ¬ K.Connected →
      ∃ a b : V, ¬ K.Adj a b ∧ ¬ K.Reachable a b) := by
  intro h
  have hnc : ¬ (⊥ : SimpleGraph PEmpty).Connected := by
    intro hc
    exact PEmpty.elim (Classical.choice hc.nonempty)
  obtain ⟨a, b, _, _⟩ := h (V := PEmpty) (K := ⊥) hnc
  exact PEmpty.elim a