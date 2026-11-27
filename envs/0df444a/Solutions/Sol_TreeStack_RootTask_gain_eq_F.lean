-- Prove2me | solution 1 for TreeStack.RootTask.gain_eq_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:05.433881+00:00
-- url     : https://prove2.me/submissions/8d9d795f-a994-4074-8926-c6a5fc51fbf4

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_RootTask_occupied
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
namespace RootTask
theorem _root_.solution
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = F (OrientedBranch.effectiveInput C t.branch) := by
  rw [RootTask.gain,
    OrientedBranch.branchMessage_eq_some_of_occupied C t.branch t.occupied]
  rfl
end RootTask
end TreeStack
