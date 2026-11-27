-- Prove2me | solution 1 for TreeStack.OrientedBranch.no_child_of_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:48:38.141237+00:00
-- url     : https://prove2.me/submissions/638e8897-9e02-414b-b4c9-c632951df658

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
    (hLeaf : T.graph.degree B.root = 1) (v : V) :
    ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
  intro h
  have huniq :
      ∃! w : V, T.graph.Adj B.root w :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hLeaf
  exact h.2 (huniq.unique h.1 B.adj)
end TreeStack.OrientedBranch
