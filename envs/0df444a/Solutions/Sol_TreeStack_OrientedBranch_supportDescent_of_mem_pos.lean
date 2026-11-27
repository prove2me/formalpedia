-- Prove2me | solution 1 for TreeStack.OrientedBranch.supportDescent_of_mem_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:10:54.803721+00:00
-- url     : https://prove2.me/submissions/83174298-03e7-4ae3-9c3c-46e8461d84d3

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_child_supportEdge_iff_occupied_of_supportEdge
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
import Theorems.Thm_TreeStack_OrientedBranch_exists_childBranch_mem_of_mem_vertices_ne_root


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) {x : V}
    (hx : x ∈ B.vertices) (hxPos : 0 < C x) :
    SupportDescent C B x := by
  classical
  by_cases hxr : x = B.root
  · subst x
    exact SupportDescent.root B
  · rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, hxChild⟩
    have hChildOcc : (B.childBranch c).Occupied C :=
      ⟨x, hxChild, hxPos⟩
    have hChildEdge : (B.childBranch c).SupportEdge C :=
      (B.child_supportEdge_iff_occupied_of_supportEdge C hEdge c).2 hChildOcc
    exact
      SupportDescent.child B c hChildEdge
        (solution
          C (B.childBranch c) hChildEdge hxChild hxPos)
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt _
end TreeStack.OrientedBranch
