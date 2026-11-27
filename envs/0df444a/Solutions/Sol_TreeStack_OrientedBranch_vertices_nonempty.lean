-- Prove2me | solution 1 for TreeStack.OrientedBranch.vertices_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:56.485323+00:00
-- url     : https://prove2.me/submissions/d1243993-2677-4445-b439-539671003cf3

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    B.vertices.Nonempty :=
  ⟨B.root, B.root_mem_vertices⟩
end TreeStack.OrientedBranch
