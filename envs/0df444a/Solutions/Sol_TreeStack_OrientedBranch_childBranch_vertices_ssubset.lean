-- Prove2me | solution 1 for TreeStack.OrientedBranch.childBranch_vertices_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:29.256067+00:00
-- url     : https://prove2.me/submissions/eff72a43-ceeb-4102-abbb-5347f84bd048

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊂ B.vertices := by
  classical
  rw [Finset.ssubset_iff_of_subset (B.childBranch_vertices_subset c)]
  refine ⟨B.root, B.root_mem_vertices, ?_⟩
  simpa using (B.childBranch c).parent_not_mem_vertices
end TreeStack.OrientedBranch
