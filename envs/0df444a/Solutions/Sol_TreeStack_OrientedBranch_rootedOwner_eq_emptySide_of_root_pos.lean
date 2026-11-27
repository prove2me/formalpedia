-- Prove2me | solution 1 for TreeStack.OrientedBranch.rootedOwner_eq_emptySide_of_root_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:10:33.424811+00:00
-- url     : https://prove2.me/submissions/f36a13f4-1682-4bfb-aa5f-75b5e6d0c7e9

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
import Theorems.Thm_TreeStack_OrientedBranch_mem_vertices_or_mem_reverseBranch
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_parent_of_mem_vertices


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T)
    (hRootPos : 0 < C ambientRoot)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    B.rootedOwner ambientRoot = B.parent := by
  have hNotReverse : ambientRoot ∉ B.reverseBranch.vertices := by
    intro hmem
    exact hEmpty ⟨ambientRoot, hmem, hRootPos⟩
  have hMem : ambientRoot ∈ B.vertices := by
    rcases B.mem_vertices_or_mem_reverseBranch ambientRoot with h | h
    · exact h
    · exact (hNotReverse h).elim
  exact B.rootedOwner_eq_parent_of_mem_vertices ambientRoot hMem
end TreeStack.OrientedBranch
