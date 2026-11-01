-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:13:59.623213+00:00
-- url     : https://prove2.me/submissions/bb867d42-61a4-48cb-b651-e23bfe674a29

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V),
      ¬ G.Connected → ∃ u v : V, ¬ G.Reachable u v) := by
  intro h
  let G : SimpleGraph (Fin 0) := ⊥
  have hG : ¬ G.Connected := by
    intro hc
    have hne : Nonempty (Fin 0) := hc.nonempty
    rcases hne with ⟨v⟩
    exact Fin.elim0 v
  rcases h G hG with ⟨u, v, huv⟩
  exact Fin.elim0 u