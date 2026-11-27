-- Prove2me | solution 1 for TreeStack.OrientedBranch.childEdge_ne_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:21.423551+00:00
-- url     : https://prove2.me/submissions/6b30bfda-83c1-4f59-906f-bb880f8cafbc

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) (c : B.Child) :
    s(B.root, c.vertex) ≠ s(B.root, B.parent) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact c.ne_parent h.2
  · exact B.root_ne_parent h.1
end TreeStack.OrientedBranch
