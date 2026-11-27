-- Prove2me | solution 1 for TreeStack.OrientedBranch.reverse_child_occupied_of_supportEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:00:12.983067+00:00
-- url     : https://prove2.me/submissions/8959893b-9342-4b08-b796-f1453c6805ed

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_vertices_disjoint_reverseBranch
import Theorems.Thm_TreeStack_OrientedBranch_mem_vertices_or_mem_reverseBranch
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).reverseBranch.Occupied C := by
  rcases hEdge.2 with ⟨y, hyReverseB, hyPos⟩
  have hyNotChild : y ∉ (B.childBranch c).vertices := by
    intro hyChild
    have hyB : y ∈ B.vertices :=
      B.childBranch_vertices_subset c hyChild
    exact
      (Finset.disjoint_left.mp B.vertices_disjoint_reverseBranch)
        hyB hyReverseB
  rcases (B.childBranch c).mem_vertices_or_mem_reverseBranch y with
    hyChild | hyReverseChild
  · exact (hyNotChild hyChild).elim
  · exact ⟨y, hyReverseChild, hyPos⟩
end TreeStack.OrientedBranch
