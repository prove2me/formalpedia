-- Prove2me | solution 1 for TreeStack.OrientedBranch.defectiveGraph_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:36.427741+00:00
-- url     : https://prove2.me/submissions/b29af62c-8e78-4960-85f0-e62076266b77

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
import Theorems.Thm_TreeStack_OrientedBranch_defectiveGraph_le_tree

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) :
    (defectiveGraph (T := T) C).IsAcyclic := by
  exact
    SimpleGraph.IsAcyclic.anti
      (defectiveGraph_le_tree (T := T) C)
      T.isTree.isAcyclic
end TreeStack.OrientedBranch
