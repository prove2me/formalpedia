-- Prove2me | solution 1 for WilliamsonShmoys.reachable_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:05.28642+00:00
-- url     : https://prove2.me/submissions/d4bf5e8c-397b-4f30-8e20-e005be9e0ba7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V} (hdis : ¬ G.Reachable u v) :
    ∃ A : Set V, u ∈ A ∧ v ∉ A ∧
      ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ G.Adj x y := by
  refine ⟨{x | G.Reachable u x}, ?_, ?_, ?_⟩
  · exact SimpleGraph.Reachable.rfl
  · exact hdis
  · intro x y hx hy hadj
    apply hy
    exact hx.trans hadj.reachable