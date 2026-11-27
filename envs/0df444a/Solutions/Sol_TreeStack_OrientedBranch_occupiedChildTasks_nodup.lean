-- Prove2me | solution 1 for TreeStack.OrientedBranch.occupiedChildTasks_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:24.789039+00:00
-- url     : https://prove2.me/submissions/1653e783-ae6a-40fa-997f-0e78860c7c67

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
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V) :
    (B.occupiedChildTasks C).Nodup := by
  classical
  exact Finset.nodup_toList (Finset.univ : Finset (B.OccupiedChild C))
end TreeStack.OrientedBranch
