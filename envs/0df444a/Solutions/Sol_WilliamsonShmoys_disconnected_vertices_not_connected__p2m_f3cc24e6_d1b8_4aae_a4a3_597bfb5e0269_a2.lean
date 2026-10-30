-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_not_connected__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:34:43.62062+00:00
-- url     : https://prove2.me/submissions/ae421710-0b20-4cb9-89d5-d21491ea6253

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDisc : ¬ G.Connected),
    ∃ u v : V, ¬ Nonempty (G.Walk u v)) := by
  intro h
  have hnc : ¬ (⊥ : SimpleGraph (Fin 0)).Connected := fun hc => hc.nonempty.elim fun v => v.elim0
  obtain ⟨u, -, -⟩ := h (⊥ : SimpleGraph (Fin 0)) hnc
  exact u.elim0
