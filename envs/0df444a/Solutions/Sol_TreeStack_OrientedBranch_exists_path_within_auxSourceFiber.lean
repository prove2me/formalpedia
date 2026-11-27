-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_path_within_auxSourceFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:06.537647+00:00
-- url     : https://prove2.me/submissions/e0957cb5-7844-4743-92a3-62da266a0a97

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
import Theorems.Thm_TreeStack_OrientedBranch_exists_walk_within_auxSourceFiber

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r x y : V)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores r) :
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧
        ∀ z ∈ p.support,
          z ∈ auxSourceFiber C ambientRoot hScores r := by
  rcases
      exists_walk_within_auxSourceFiber
        C ambientRoot hScores r x y hx hy with
    ⟨w, hw⟩
  refine ⟨w.toPath, w.toPath.2, ?_⟩
  intro z hz
  exact hw z (w.support_toPath_subset_support hz)
end TreeStack.OrientedBranch
