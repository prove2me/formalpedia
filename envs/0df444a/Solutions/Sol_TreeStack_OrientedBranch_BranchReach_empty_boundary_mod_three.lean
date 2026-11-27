-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.empty_boundary_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:55:19.19131+00:00
-- url     : https://prove2.me/submissions/e58e5174-1cd2-4a06-a8cb-71da7c17e83b

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_signedCarrierMass_modEq
import Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_withBoundary_eq_of_not_occupied
import Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_eq_parent_of_cleared

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
    (D B.parent : ℤ) ≡ (q : ℤ) [ZMOD 3] := by
  have hmod := BranchReach.signedCarrierMass_modEq B hreach
  rw [B.signedCarrierMass_eq_parent_of_cleared D hClear,
    B.signedCarrierMass_withBoundary_eq_of_not_occupied C q hEmpty] at hmod
  exact hmod
end BranchReach
end TreeStack.OrientedBranch
