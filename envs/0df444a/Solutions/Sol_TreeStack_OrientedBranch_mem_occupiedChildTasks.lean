-- Prove2me | solution 1 for TreeStack.OrientedBranch.mem_occupiedChildTasks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:45.061322+00:00
-- url     : https://prove2.me/submissions/512e2f9f-88a9-4cac-9fee-b596c64b3807

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
    (B : OrientedBranch T) (C : Configuration V)
    (t : B.OccupiedChild C) :
    t ∈ B.occupiedChildTasks C := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ t)
end TreeStack.OrientedBranch
