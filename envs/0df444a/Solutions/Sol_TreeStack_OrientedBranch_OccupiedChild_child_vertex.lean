-- Prove2me | solution 1 for TreeStack.OrientedBranch.OccupiedChild.child_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:44.512799+00:00
-- url     : https://prove2.me/submissions/2396b7b5-8c5f-4517-bbd5-e1d8136b6fd6

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
    t.child.vertex = t.1 := rfl
end OccupiedChild
end TreeStack.OrientedBranch
