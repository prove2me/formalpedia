-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:18.94316+00:00
-- url     : https://prove2.me/submissions/72923964-3202-4b3e-b621-8268f10fb803

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ A B : Set V,
      (∀ x, x ∈ A ∨ x ∈ B) ∧
      Disjoint A B ∧
      u ∈ A ∧
      v ∈ B ∧
      (∀ x y, G.Adj x y → (x ∈ A ↔ y ∈ A)) := by
  classical
  let A : Set V := {x | G.Reachable u x}
  let B : Set V := {x | ¬ G.Reachable u x}
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : G.Reachable u x
    · exact Or.inl hx
    · exact Or.inr hx
  · exact Set.disjoint_left.mpr (by
      intro x hxA hxB
      exact hxB hxA)
  · exact SimpleGraph.Reachable.refl (G := G) u
  · exact hnot
  · intro x y hxy
    constructor
    · intro hxA
      exact SimpleGraph.Reachable.trans hxA (SimpleGraph.Adj.reachable hxy)
    · intro hyA
      exact SimpleGraph.Reachable.trans hyA
        (SimpleGraph.Adj.reachable hxy.symm)