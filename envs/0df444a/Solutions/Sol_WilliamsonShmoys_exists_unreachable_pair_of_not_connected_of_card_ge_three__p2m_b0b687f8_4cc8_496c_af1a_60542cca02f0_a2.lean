-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair_of_not_connected_of_card_ge_three__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:33.566257+00:00
-- url     : https://prove2.me/submissions/7ed11e9e-2fc5-45ea-a6c2-915c566fca00

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (h : ¬ G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ u v : V, ¬ G.Reachable u v := by
  rw [SimpleGraph.connected_iff] at h
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hpre : ¬ G.Preconnected := by
    intro hp
    exact h ⟨hp, ‹Nonempty V›⟩
  change ¬ (∀ u v : V, G.Reachable u v) at hpre
  push_neg at hpre
  exact hpre