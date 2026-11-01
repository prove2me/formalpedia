-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:25.969523+00:00
-- url     : https://prove2.me/submissions/3a43966f-7fb6-413a-b8ae-a71cf8c2ace4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj],
    ¬ H.Connected → ∃ u v : V, ¬ H.Reachable u v) := by
  intro h
  have hDisconnected : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact Fin.elim0 v
  obtain ⟨u, v, _⟩ := h (V := Fin 0) (⊥ : SimpleGraph (Fin 0)) hDisconnected
  exact Fin.elim0 u