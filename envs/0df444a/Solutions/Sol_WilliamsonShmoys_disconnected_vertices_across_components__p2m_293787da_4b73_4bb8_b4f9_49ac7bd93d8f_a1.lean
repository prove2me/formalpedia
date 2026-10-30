-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_across_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:40:11.47797+00:00
-- url     : https://prove2.me/submissions/1a539d8d-d0a3-4f9c-b282-503ec7158556

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V), ¬ G.Connected →
        ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v) := by
  intro h
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  let G : SimpleGraph Empty := ⊥
  have hdis : ¬ G.Connected := by
    intro hc
    exact isEmptyElim (Classical.choice hc.nonempty)
  obtain ⟨u, v, _, _⟩ := h G hdis
  exact isEmptyElim u