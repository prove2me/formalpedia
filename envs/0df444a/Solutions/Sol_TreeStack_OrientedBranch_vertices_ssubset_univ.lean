-- Prove2me | solution 1 for TreeStack.OrientedBranch.vertices_ssubset_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:12.937457+00:00
-- url     : https://prove2.me/submissions/a872ea36-7aab-4cf5-95a3-a896479f2fbb

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    B.vertices ⊂ (Finset.univ : Finset V) := by
  classical
  rw [Finset.ssubset_iff_of_subset (Finset.subset_univ B.vertices)]
  exact ⟨B.parent, Finset.mem_univ _, B.parent_not_mem_vertices⟩
end TreeStack.OrientedBranch
