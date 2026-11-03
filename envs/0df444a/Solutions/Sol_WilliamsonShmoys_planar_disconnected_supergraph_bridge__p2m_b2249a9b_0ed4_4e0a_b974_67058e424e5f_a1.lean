-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_supergraph_bridge__p2m_b2249a9b_0ed4_4e0a_b974_67058e424e5f_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:50:48.590142+00:00
-- url     : https://prove2.me/submissions/52f9998c-6fba-4a65-9389-595e747ef41e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    HasPlanarDrawingOn G → ¬ G.Connected →
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) := by
  intro h
  let G : SimpleGraph (Fin 0) := ⊥
  have hp : HasPlanarDrawingOn G := by
    refine ⟨fun _ => (0, 0), fun _ _ _ => (0, 0), ?_, ?_, ?_⟩
    · intro u
      exact Fin.elim0 u
    · intro u
      exact Fin.elim0 u
    · intro u
      exact Fin.elim0 u
  have hd : ¬ G.Connected := by
    intro hc
    obtain ⟨u⟩ := hc.nonempty
    exact Fin.elim0 u
  obtain ⟨H, _, _, u, _, _, _⟩ := h G hp hd
  exact Fin.elim0 u
