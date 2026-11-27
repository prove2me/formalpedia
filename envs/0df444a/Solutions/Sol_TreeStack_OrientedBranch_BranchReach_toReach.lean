-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.toReach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:41.798892+00:00
-- url     : https://prove2.me/submissions/4f9ecf61-bda4-4cbb-96c6-5b315d814d31

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
namespace OrientedBranch.BranchReach
theorem _root_.solution
    [DecidableEq V] (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    Reach T.graph C D := by
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hED with ⟨u, v, huv, hlegal, huCarrier, hvCarrier, rfl⟩
      exact ⟨u, v, huv, hlegal, rfl⟩
end OrientedBranch.BranchReach
end TreeStack
