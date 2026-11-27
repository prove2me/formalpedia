-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_child_supportEdge_of_supportEdge_of_root_not_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:11:34.870918+00:00
-- url     : https://prove2.me/submissions/8a79d32a-36ad-4766-b527-82bd37f29de5

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_child_supportEdge_iff_occupied_of_supportEdge
import Theorems.Thm_TreeStack_OrientedBranch_exists_childBranch_mem_of_mem_vertices_ne_root


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (hRoot : ¬ 0 < C B.root) :
    ∃ c : B.Child, (B.childBranch c).SupportEdge C := by
  rcases hEdge.1 with ⟨x, hxB, hxPos⟩
  have hxNe : x ≠ B.root := by
    intro hxr
    subst x
    exact hRoot hxPos
  rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hxB hxNe with
    ⟨c, hxChild⟩
  refine ⟨c, ?_⟩
  exact
    (B.child_supportEdge_iff_occupied_of_supportEdge C hEdge c).2
      ⟨x, hxChild, hxPos⟩
end TreeStack.OrientedBranch
