-- Prove2me | solution 1 for TreeStack.OrientedBranch.card_lt_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:19.94538+00:00
-- url     : https://prove2.me/submissions/55803419-0856-4110-8e21-8d283f53ac9e

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_vertices_ssubset_univ
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    B.card < Fintype.card V := by
  classical
  simpa [card] using Finset.card_lt_card B.vertices_ssubset_univ
end TreeStack.OrientedBranch
