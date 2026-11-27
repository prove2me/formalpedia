-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.of_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:49.83601+00:00
-- url     : https://prove2.me/submissions/6f0eac78-30d5-4d08-b5e5-b2d51d7e24db

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_carrier_subset

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace BranchReach
theorem _root_.solution
    (B : OrientedBranch T) (c : B.Child)
    {C D : Configuration V}
    (hreach : (B.childBranch c).BranchReach C D) :
    B.BranchReach C D := by
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hED with ⟨u, v, huv, hlegal, hu, hv, rfl⟩
      exact
        ⟨u, v, huv, hlegal,
          B.childBranch_carrier_subset c hu,
          B.childBranch_carrier_subset c hv, rfl⟩
end BranchReach
end TreeStack.OrientedBranch
