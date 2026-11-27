-- Prove2me | solution 1 for TreeStack.OrientedBranch.OccupiedChild.gain_eq_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:06.621274+00:00
-- url     : https://prove2.me/submissions/6805a957-9c24-4185-bf7b-d3d84f6a5ed4

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace OccupiedChild
theorem _root_.solution
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = F (effectiveInput C (B.childBranch t.child)) := by
  rw [OccupiedChild.gain,
    branchMessage_eq_some_of_occupied C (B.childBranch t.child) t.occupied]
  rfl
end OccupiedChild
end TreeStack.OrientedBranch
