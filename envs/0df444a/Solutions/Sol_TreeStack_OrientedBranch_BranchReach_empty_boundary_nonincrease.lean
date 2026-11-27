-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.empty_boundary_nonincrease
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:53:17.342319+00:00
-- url     : https://prove2.me/submissions/7f5aa77e-41dd-412f-b04d-830184ad4d34

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_carrierMass_le
import Theorems.Thm_TreeStack_OrientedBranch_carrierMass_withBoundary_eq_of_not_occupied
import Theorems.Thm_TreeStack_OrientedBranch_carrierMass_eq_parent_of_cleared

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace BranchReach
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hreach : B.BranchReach (B.withBoundary C q) D)
    (hClear : B.Cleared D) :
    D B.parent ≤ q := by
  have hle := BranchReach.carrierMass_le B hreach
  rw [B.carrierMass_eq_parent_of_cleared D hClear,
    B.carrierMass_withBoundary_eq_of_not_occupied C q hEmpty] at hle
  exact hle
end BranchReach
end TreeStack.OrientedBranch
