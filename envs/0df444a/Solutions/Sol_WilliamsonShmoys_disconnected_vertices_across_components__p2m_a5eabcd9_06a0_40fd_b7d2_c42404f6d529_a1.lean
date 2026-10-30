-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_across_components__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:29.683973+00:00
-- url     : https://prove2.me/submissions/fa6fd4c3-dee0-42b2-8d41-3f7479434c2b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (K : SimpleGraph V) (hDisconnected : ¬ K.Connected),
      ∃ u v : V, u ≠ v ∧ ¬ K.Reachable u v) := by
  intro h
  have hDisconnected : ¬ (⊥ : SimpleGraph Empty).Connected := by
    intro hConnected
    exact Empty.elim (Classical.choice hConnected.nonempty)
  rcases h (⊥ : SimpleGraph Empty) hDisconnected with ⟨u, v, _⟩
  exact Empty.elim u