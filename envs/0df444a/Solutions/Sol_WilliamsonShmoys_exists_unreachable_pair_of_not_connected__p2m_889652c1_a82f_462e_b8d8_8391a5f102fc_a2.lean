-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:57.435754+00:00
-- url     : https://prove2.me/submissions/a6c69a02-1078-447a-9d9f-99de5dcd211c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V),
    ¬ G.Connected → ∃ u v : V, ¬ G.Reachable u v) := by
  intro h
  let G : SimpleGraph Empty := ⊥
  have hdisconnected : ¬ G.Connected := by
    intro hc
    exact Empty.elim (Classical.choice hc.nonempty)
  have hpairs := h (V := Empty) G hdisconnected
  exact hpairs.elim (fun u _ => by cases u)