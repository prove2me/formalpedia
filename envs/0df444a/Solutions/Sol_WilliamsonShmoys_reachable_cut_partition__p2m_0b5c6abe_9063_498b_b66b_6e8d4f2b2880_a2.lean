-- Prove2me | solution 1 for WilliamsonShmoys.reachable_cut_partition__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:01:39.353839+00:00
-- url     : https://prove2.me/submissions/cc91570d-717c-4eed-b63c-559cab783c93

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hsep : ¬ G.Reachable u v) :
    ∃ S : Set V, u ∈ S ∧ v ∉ S ∧
      ∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬ G.Adj a b := by
  classical
  let S : Set V := {x | G.Reachable u x}
  refine ⟨S, ?_, ?_, ?_⟩
  · change G.Reachable u u
    exact SimpleGraph.Reachable.refl u
  · change ¬ G.Reachable u v
    exact hsep
  · intro a b ha hb hab
    apply hb
    change G.Reachable u b
    exact (show G.Reachable u a from ha).trans hab.reachable