-- Prove2me | solution 1 for TreeStack.OrientedBranch.child_nonempty_of_internal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:57:51.40883+00:00
-- url     : https://prove2.me/submissions/d4b5b0d5-146a-4fa8-a6a4-a10cd9bd5d9d

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    Nonempty B.Child := by
  by_contra hnone
  have huniq : ∃! w : V, T.graph.Adj B.root w := by
    refine ⟨B.parent, B.adj, ?_⟩
    intro y hy
    by_contra hyne
    exact hnone
      ⟨{ vertex := y
         adj := hy
         ne_parent := hyne }⟩
  have hdeg :
      T.graph.degree B.root = 1 :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr huniq
  omega
end TreeStack.OrientedBranch
