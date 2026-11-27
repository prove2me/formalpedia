-- Prove2me | solution 1 for TreeStack.OrientedBranch.signature_branchFlux_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:54:46.58874+00:00
-- url     : https://prove2.me/submissions/23dde9d1-d65c-439f-8c5d-3f6bdf829f9d

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
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_not_occupied_iff_zero_on_vertices
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_root_balance_with_child_flux
import Theorems.Thm_TreeStack_OrientedBranch_exists_nat_three_loss
import Theorems.Thm_TreeStack_OrientedBranch_F_sub_three_mul_le
import Theorems.Thm_TreeStack_OrientedBranch_F_sub_three_mul_mod_three
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
import Theorems.Thm_TreeStack_one_vertex_flux_le
import Theorems.Thm_TreeStack_one_vertex_flux_mod_three
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
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.boundaryParityWeight_parent

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hClears : MoveSignature.Clears m C B)
    (hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A) :
    (B.Occupied C →
      MoveSignature.boundaryFlux m B ≤ F (effectiveInput C B) ∧
      MoveSignature.boundaryFlux m B % 3 =
        F (effectiveInput C B) % 3) ∧
    (¬ B.Occupied C →
      ∃ k : ℕ,
        MoveSignature.boundaryFlux m B = -3 * (k : ℤ)) := by
  classical
  have hChildLoss :
      ∀ v : V,
        ∃ k : ℕ,
          (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ) -
                2 * (m.count B.root v : ℤ)
            else
              0) =
            (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                messageContribution
                  (branchMessage C
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }))
              else
                0) -
              3 * (k : ℤ) := by
    intro v
    by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
    · let c : B.Child :=
        { vertex := v
          adj := h.1
          ne_parent := h.2 }
      have hChildClears :
          MoveSignature.Clears m C (B.childBranch c) := by
        intro w hw
        exact hClears w (B.childBranch_vertices_subset c hw)
      have hChildCausal :
          ∀ A : OrientedBranch T,
            A.vertices ⊆ (B.childBranch c).vertices →
            A.Occupied C →
            MoveSignature.CausalOutward m A := by
        intro A hA hOcc
        apply hCausal A
        intro w hw
        exact B.childBranch_vertices_subset c (hA hw)
        exact hOcc
      have hRec :=
        solution m C (B.childBranch c)
          hChildClears hChildCausal
      by_cases hOcc : (B.childBranch c).Occupied C
      · have hBound := hRec.1 hOcc
        rcases exists_nat_three_loss hBound.1 hBound.2 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmsg :=
          branchMessage_eq_some_of_occupied C (B.childBranch c) hOcc
        simpa [h, c, MoveSignature.boundaryFlux, hmsg] using hk
      · rcases hRec.2 hOcc with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmsg :=
          branchMessage_eq_empty_of_not_occupied C (B.childBranch c) hOcc
        simpa [h, c, MoveSignature.boundaryFlux, hmsg] using hk
    · refine ⟨0, ?_⟩
      simp [h]
  choose k hk using hChildLoss
  let K : ℕ := ∑ v : V, k v
  have hK :
      (K : ℤ) = ∑ v : V, (k v : ℤ) := by
    simp [K]
  have hChildSum :
      signatureChildFluxSum m B =
        childMessageSum C B - 3 * (K : ℤ) := by
    rw [signatureChildFluxSum, childMessageSum]
    calc
      (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
        else
          0) =
          ∑ v : V,
            ((if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                messageContribution
                  (branchMessage C
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }))
              else
                0) - 3 * (k v : ℤ)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact hk v
      _ =
          (∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              messageContribution
                (branchMessage C
                  (B.childBranch
                    { vertex := v
                      adj := h.1
                      ne_parent := h.2 }))
            else
              0) -
            3 * (∑ v : V, (k v : ℤ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = childMessageSum C B - 3 * (K : ℤ) := by
        rw [childMessageSum, hK]
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent <;> simp [h]
  have hRoot :=
    MoveSignature.root_balance_with_child_flux m C B
      (hClears B.root B.root_mem_vertices)
  have hBal :
      (effectiveInput C B - 3 * (K : ℤ)) +
          (m.count B.parent B.root : ℤ) -
        2 * (m.count B.root B.parent : ℤ) = 0 := by
    rw [hChildSum] at hRoot
    rw [effectiveInput]
    omega
  constructor
  · intro hOcc
    have hOut :=
      hCausal B (by intro w hw; exact hw) hOcc
    have hA : 1 ≤ (m.count B.root B.parent : ℤ) := by
      exact_mod_cast hOut
    have hIn : 0 ≤ (m.count B.parent B.root : ℤ) := by
      positivity
    have hLocalLe :=
      one_vertex_flux_le
        (y := effectiveInput C B - 3 * (K : ℤ))
        (A := (m.count B.root B.parent : ℤ))
        (B := (m.count B.parent B.root : ℤ))
        hA hIn hBal
    have hLocalMod :=
      one_vertex_flux_mod_three
        (y := effectiveInput C B - 3 * (K : ℤ))
        (A := (m.count B.root B.parent : ℤ))
        (B := (m.count B.parent B.root : ℤ))
        hA hIn hBal
    constructor
    · rw [MoveSignature.boundaryFlux]
      exact hLocalLe.trans
        (F_sub_three_mul_le (effectiveInput C B) K)
    · rw [MoveSignature.boundaryFlux]
      calc
        ((m.count B.root B.parent : ℤ) -
              2 * (m.count B.parent B.root : ℤ)) % 3 =
            F (effectiveInput C B - 3 * (K : ℤ)) % 3 :=
          hLocalMod
        _ = F (effectiveInput C B) % 3 :=
          F_sub_three_mul_mod_three (effectiveInput C B) K
  · intro hEmpty
    have hZero :=
      (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
    have hRootZero : C B.root = 0 :=
      hZero B.root B.root_mem_vertices
    have hChildMessageZero : childMessageSum C B = 0 := by
      rw [childMessageSum]
      apply Finset.sum_eq_zero
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hChildEmpty : ¬ (B.childBranch c).Occupied C := by
          rintro ⟨w, hw, hwpos⟩
          exact hEmpty
            ⟨w, B.childBranch_vertices_subset c hw, hwpos⟩
        have hmsg :=
          branchMessage_eq_empty_of_not_occupied C (B.childBranch c)
            hChildEmpty
        simp [h, c, hmsg]
      · simp [h]
    rw [hChildSum] at hRoot
    simp [hRootZero, hChildMessageZero] at hRoot
    refine ⟨m.count B.root B.parent + 2 * K, ?_⟩
    rw [MoveSignature.boundaryFlux]
    push_cast
    omega
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c
end TreeStack.OrientedBranch
