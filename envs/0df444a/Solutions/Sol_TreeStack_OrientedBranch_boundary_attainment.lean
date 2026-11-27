-- Prove2me | solution 1 for TreeStack.OrientedBranch.boundary_attainment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:03.291587+00:00
-- url     : https://prove2.me/submissions/d1b42d9c-38f0-4d8c-89ba-76d54b5a6c20

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_orderedTasks_safe
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_repeat_move
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_taskGainSum_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_executeAllOccupiedChildren
import Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_even
import Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_ge_two
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_F_of_le_one
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
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
    (C : Configuration V) (B : OrientedBranch T)
    (hOcc : B.Occupied C) :
    ∀ d : ℤ, branchMessage C B = some d →
      ∀ q : ℕ, 0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          B.ClearOutcome C q D ∧
            (D B.parent : ℤ) = (q : ℤ) + d := by
  classical
  intro d hMsg q hPos
  have hCanonical :=
    branchMessage_eq_some_of_occupied C B hOcc
  have hd : d = F (effectiveInput C B) := by
    rw [hCanonical] at hMsg
    exact (Option.some.inj hMsg).symm
  have hFinalF :
      0 < (q : ℤ) + F (effectiveInput C B) := by
    simpa [hd] using hPos
  have hChildAttain :
      ∀ (c : B.Child) (E : Configuration V) (d' : ℤ) (q' : ℕ),
        (B.childBranch c).Occupied E →
        branchMessage E (B.childBranch c) = some d' →
        0 < (q' : ℤ) + d' →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E q' D ∧
            (D B.root : ℤ) = (q' : ℤ) + d' := by
    intro c E d' q' hOcc' hMsg' hPos'
    exact solution E (B.childBranch c)
      hOcc' d' hMsg' q' hPos'
  by_cases hy : effectiveInput C B ≤ 1
  · have hF :
        F (effectiveInput C B) =
          2 * effectiveInput C B - 3 :=
      F_of_le_one hy
    have hbNonneg :
        0 ≤ 2 - effectiveInput C B := by
      omega
    let b : ℕ := (2 - effectiveInput C B).toNat
    have hbCast :
        (b : ℤ) = 2 - effectiveInput C B := by
      change (((2 - effectiveInput C B).toNat : ℕ) : ℤ) =
        2 - effectiveInput C B
      rw [Int.toNat_of_nonneg hbNonneg]
    have hqEnoughZ :
        2 * (b : ℤ) ≤ (q : ℤ) := by
      rw [hF] at hFinalF
      rw [hbCast]
      omega
    have hqEnough : 2 * b ≤ q := by
      exact_mod_cast hqEnoughZ
    have hPreEnough :
        2 * b ≤ (B.withBoundary C q) B.parent := by
      simpa using hqEnough
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier
        (B.withBoundary C q) b hPreEnough with
      ⟨Epre, hPreReach, hPreParent, hPreRoot, hPreOther⟩
    have hPreRootNat :
        Epre B.root = C B.root + b := by
      simpa [B.withBoundary_of_mem_vertices C q
        B.root_mem_vertices] using hPreRoot
    have hPreRootZ :
        (Epre B.root : ℤ) =
          (C B.root : ℤ) + (b : ℤ) := by
      exact_mod_cast hPreRootNat
    have hScheduleFinal :
        (Epre B.root : ℤ) + childMessageSum C B = 2 := by
      calc
        (Epre B.root : ℤ) + childMessageSum C B =
            (C B.root : ℤ) + (b : ℤ) +
              childMessageSum C B := by rw [hPreRootZ]
        _ = effectiveInput C B + (b : ℤ) := by
              rw [effectiveInput]
              ring
        _ = 2 := by
              rw [hbCast]
              ring
    have hSamePre :
        ∀ v ∈ B.vertices, v ≠ B.root → Epre v = C v := by
      intro v hv hvRoot
      have hvParent : v ≠ B.parent := by
        intro hvp
        subst v
        exact B.parent_not_mem_vertices hv
      calc
        Epre v = B.withBoundary C q v :=
          hPreOther v hvParent hvRoot
        _ = C v := B.withBoundary_of_mem_vertices C q hv
    have hSafe :
        TaskScheduleSafe
          (fun t : B.OccupiedChild C => t.gain)
          (Epre B.root : ℤ)
          (orderedTasks
            (fun t : B.OccupiedChild C => t.gain)
            (B.occupiedChildTasks C)) := by
      apply orderedTasks_safe
      · positivity
      · rw [taskGainSum_occupiedChildTasks]
        omega
    rcases B.executeAllOccupiedChildren C Epre hChildAttain
        hSamePre hSafe with
      ⟨E₁, hChildReach, hChildRoot, hChildParent, hNonroot⟩
    have hE₁RootZ : (E₁ B.root : ℤ) = 2 := by
      calc
        (E₁ B.root : ℤ) =
            (Epre B.root : ℤ) + childMessageSum C B :=
          hChildRoot
        _ = 2 := hScheduleFinal
    have hE₁Root : E₁ B.root = 2 := by
      exact_mod_cast hE₁RootZ
    rcases B.attainRootTransfer_even E₁ 1 (by omega)
        hE₁Root hNonroot with
      ⟨D, hRootReach, hCleared, hDParent⟩
    have hPreParentNat :
        Epre B.parent = q - 2 * b := by
      simpa [B.withBoundary_parent C q] using hPreParent
    have hPreParentZ :
        (Epre B.parent : ℤ) =
          (q : ℤ) - 2 * (b : ℤ) := by
      calc
        (Epre B.parent : ℤ) = ((q - 2 * b : ℕ) : ℤ) := by
          exact_mod_cast hPreParentNat
        _ = (q : ℤ) - 2 * (b : ℤ) := by
          rw [Nat.cast_sub hqEnough]
          norm_num
    have hParentFinal :
        (D B.parent : ℤ) = (q : ℤ) + d := by
      rw [hDParent, hChildParent, hE₁RootZ, F_two,
        hPreParentZ, hd, hF, hbCast]
      ring
    have hReach :
        B.BranchReach (B.withBoundary C q) D :=
      Relation.ReflTransGen.trans hPreReach
        (Relation.ReflTransGen.trans hChildReach hRootReach)
    exact ⟨D, ⟨hReach, hCleared⟩, hParentFinal⟩
  · have hyTwo : 2 ≤ effectiveInput C B := by
      omega
    have hyPos : 0 < effectiveInput C B := by
      omega
    have hSafe :
        TaskScheduleSafe
          (fun t : B.OccupiedChild C => t.gain)
          ((B.withBoundary C q) B.root : ℤ)
          (orderedTasks
            (fun t : B.OccupiedChild C => t.gain)
            (B.occupiedChildTasks C)) := by
      apply orderedTasks_safe
      · positivity
      · rw [taskGainSum_occupiedChildTasks,
          B.withBoundary_of_mem_vertices C q B.root_mem_vertices]
        simpa [effectiveInput] using hyPos
    have hSame :
        ∀ v ∈ B.vertices, v ≠ B.root →
          B.withBoundary C q v = C v := by
      intro v hv hvr
      exact B.withBoundary_of_mem_vertices C q hv
    rcases B.executeAllOccupiedChildren C (B.withBoundary C q)
        hChildAttain hSame hSafe with
      ⟨E₁, hChildReach, hChildRoot, hChildParent, hNonroot⟩
    have hE₁RootZ :
        (E₁ B.root : ℤ) = effectiveInput C B := by
      calc
        (E₁ B.root : ℤ) =
            ((B.withBoundary C q) B.root : ℤ) +
              childMessageSum C B := hChildRoot
        _ = effectiveInput C B := by
              rw [B.withBoundary_of_mem_vertices C q
                B.root_mem_vertices]
              rfl
    have hE₁RootTwo : 2 ≤ E₁ B.root := by
      have hz : (2 : ℤ) ≤ (E₁ B.root : ℤ) := by
        rw [hE₁RootZ]
        exact hyTwo
      exact_mod_cast hz
    have hE₁Parent : E₁ B.parent = q := by
      rw [hChildParent, B.withBoundary_parent C q]
    have hTransferPos :
        0 < (E₁ B.parent : ℤ) + F (E₁ B.root : ℤ) := by
      rw [hE₁Parent, hE₁RootZ]
      exact hFinalF
    rcases B.attainRootTransfer_ge_two E₁ hE₁RootTwo
        hNonroot hTransferPos with
      ⟨D, hRootReach, hCleared, hDParent⟩
    have hParentFinal :
        (D B.parent : ℤ) = (q : ℤ) + d := by
      rw [hDParent, hE₁Parent, hE₁RootZ, hd]
    have hReach :
        B.BranchReach (B.withBoundary C q) D :=
      Relation.ReflTransGen.trans hChildReach hRootReach
    exact ⟨D, ⟨hReach, hCleared⟩, hParentFinal⟩
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c
end TreeStack.OrientedBranch
