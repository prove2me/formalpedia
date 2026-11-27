-- Prove2me | solution 1 for TreeStack.OrientedBranch.card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:15.294537+00:00
-- url     : https://prove2.me/submissions/451737f6-d16a-4ce6-a75c-73fcfb919a08

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_vertices_nonempty
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) : 0 < B.card := by
  classical
  simpa [card] using Finset.card_pos.mpr B.vertices_nonempty
end TreeStack.OrientedBranch
