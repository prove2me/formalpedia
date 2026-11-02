-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_separated_pair__p2m_46cfe7ce_b627_4e5a_9d08_1eab5cbb77ec_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T19:02:35.765253+00:00
-- url     : https://prove2.me/submissions/4ec77634-e080-4302-b2ad-e66a8f140bee

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hdis : ¬ M.Connected) :
    ∃ u v : V, ¬ M.Reachable u v ∧ ¬ M.Adj u v := by
  classical
  have hpair : ∃ u v : V, ¬ M.Reachable u v := by
    by_contra h
    have hall : ∀ u v : V, M.Reachable u v := by
      intro u v
      by_contra hreach
      exact h ⟨u, v, hreach⟩
    have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    letI : Nonempty V := hne
    exact hdis ⟨hall⟩
  obtain ⟨u, v, hnot⟩ := hpair
  refine ⟨u, v, hnot, ?_⟩
  intro hadj
  exact hnot hadj.reachable
