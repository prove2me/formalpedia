-- Prove2me | solution 1 for TreeStack.OrientedBranch.branchMessage_congr_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:45.944222+00:00
-- url     : https://prove2.me/submissions/78717e25-0034-4e2d-a994-414960ab6882

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_occupied_congr_vertices
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_empty_of_not_occupied
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C D : Configuration V) (B : OrientedBranch T)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    branchMessage C B = branchMessage D B := by
  have hOcc := B.occupied_congr_vertices C D hCD
  by_cases hC : B.Occupied C
  · have hD : B.Occupied D := hOcc.mp hC
    have hRoot : (C B.root : ℤ) = (D B.root : ℤ) := by
      exact_mod_cast hCD B.root B.root_mem_vertices
    have hChild :
        childMessageSum C B = childMessageSum D B := by
      rw [childMessageSum, childMessageSum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hSub :
            ∀ w ∈ (B.childBranch c).vertices, C w = D w := by
          intro w hw
          exact hCD w (B.childBranch_vertices_subset c hw)
        have hRec :=
          solution C D (B.childBranch c) hSub
        simp [h, c, hRec]
      · simp [h]
    rw [branchMessage_eq_some_of_occupied C B hC,
      branchMessage_eq_some_of_occupied D B hD]
    congr 2
    rw [effectiveInput, effectiveInput, hRoot, hChild]
  · have hD : ¬ B.Occupied D := by
      intro hD
      exact hC (hOcc.mpr hD)
    rw [branchMessage_eq_empty_of_not_occupied C B hC,
      branchMessage_eq_empty_of_not_occupied D B hD]
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c
end TreeStack.OrientedBranch
