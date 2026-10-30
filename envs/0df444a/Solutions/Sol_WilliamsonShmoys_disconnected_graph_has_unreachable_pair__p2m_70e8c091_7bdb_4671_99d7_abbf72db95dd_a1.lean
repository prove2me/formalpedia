-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:22:05.501735+00:00
-- url     : https://prove2.me/submissions/896e0f0f-c8a6-4bbc-9854-3eec920fbb98

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (G : SimpleGraph V) (hdis : ¬ G.Connected),
        ∃ u v : V, ¬ G.Reachable u v) := by
  intro h
  let G : SimpleGraph (Fin 0) := ⊥
  have hdis : ¬ G.Connected := by
    intro hc
    rcases hc.nonempty with ⟨v⟩
    exact Fin.elim0 v
  have hex := h (V := Fin 0) G hdis
  rcases hex with ⟨u, v, _⟩
  exact Fin.elim0 u