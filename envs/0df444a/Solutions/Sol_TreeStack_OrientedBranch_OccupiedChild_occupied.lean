-- Prove2me | solution 1 for TreeStack.OrientedBranch.OccupiedChild.occupied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:50.670558+00:00
-- url     : https://prove2.me/submissions/c3ca02b7-bfcb-4e67-98a0-05c2289cccca

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary

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
    (B.childBranch t.child).Occupied C := by
  exact Classical.choose_spec t.2
end OccupiedChild
end TreeStack.OrientedBranch
