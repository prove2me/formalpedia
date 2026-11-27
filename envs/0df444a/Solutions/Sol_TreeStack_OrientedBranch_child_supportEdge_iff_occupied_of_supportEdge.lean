-- Prove2me | solution 1 for TreeStack.OrientedBranch.child_supportEdge_iff_occupied_of_supportEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:03:14.973619+00:00
-- url     : https://prove2.me/submissions/1a077be9-dba7-4c9b-89c3-b61e4d27e797

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_reverse_child_occupied_of_supportEdge

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).SupportEdge C ↔
      (B.childBranch c).Occupied C := by
  constructor
  · intro hChild
    exact hChild.1
  · intro hChildOcc
    exact
      ⟨hChildOcc,
        B.reverse_child_occupied_of_supportEdge C hEdge c⟩
end TreeStack.OrientedBranch
