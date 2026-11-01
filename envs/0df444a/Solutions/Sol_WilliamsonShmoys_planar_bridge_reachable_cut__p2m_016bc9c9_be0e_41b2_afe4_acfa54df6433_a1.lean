-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_reachable_cut__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:07.797613+00:00
-- url     : https://prove2.me/submissions/a7b2e395-4a26-4ae0-ad19-2e0d9071967e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ s : Set V, u ∈ s ∧ v ∉ s ∧
      ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s) := by
  refine ⟨{z | G.Reachable u z}, ?_, ?_, ?_⟩
  · exact SimpleGraph.Reachable.refl u
  · exact hUnreachable
  · intro x y hxy
    constructor
    · intro hx
      exact hx.trans (SimpleGraph.Adj.reachable hxy)
    · intro hy
      exact hy.trans (SimpleGraph.Adj.reachable hxy.symm)