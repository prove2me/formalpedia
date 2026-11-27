-- Prove2me | solution 1 for TreeStack.OrientedBranch.executeOccupiedTaskSchedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:41:56.92107+00:00
-- url     : https://prove2.me/submissions/bca951e2-b310-40d3-97e1-0e447dd87666

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
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_congr_vertices
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_childBranch_carrier
import Theorems.Thm_TreeStack_OrientedBranch_mem_childBranch_vertices_not_mem_sibling_carrier
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_eq_of_not_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_of_child
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_F
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
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
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E →
        branchMessage E (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E q D ∧
            (D B.root : ℤ) = (q : ℤ) + d) :
    ∀ (tasks : List (B.OccupiedChild C)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v) →
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ) tasks →
      ∃ D : Configuration V,
        B.BranchReach E D ∧
        (D B.root : ℤ) =
          (E B.root : ℤ) +
            taskGainSum
              (fun t : B.OccupiedChild C => t.gain) tasks ∧
        D B.parent = E B.parent ∧
        (∀ t ∈ tasks, (B.childBranch t.child).Cleared D) ∧
        (∀ c : B.Child,
          (∀ t ∈ tasks, t.1 ≠ c.vertex) →
          ∀ v ∈ (B.childBranch c).vertices, D v = E v) := by
  classical
  intro tasks
  induction tasks with
  | nil =>
      intro E hNodup hSame hSafe
      refine ⟨E, Relation.ReflTransGen.refl, ?_, rfl, ?_, ?_⟩
      · simp [taskGainSum]
      · intro t ht
        simp at ht
      · intro c hnot v hv
        rfl
  | cons t ts ih =>
      intro E hNodup hSame hSafe
      have hNodupData := List.nodup_cons.mp hNodup
      have htNot : t ∉ ts := hNodupData.1
      have hNodupTail : ts.Nodup := hNodupData.2
      change
        0 < (E B.root : ℤ) + t.gain ∧
          TaskScheduleSafe
            (fun s : B.OccupiedChild C => s.gain)
            ((E B.root : ℤ) + t.gain) ts at hSafe
      have hSameHead :
          ∀ v ∈ (B.childBranch t.child).vertices, E v = C v :=
        hSame t (by simp)
      have hCE :
          ∀ v ∈ (B.childBranch t.child).vertices, C v = E v := by
        intro v hv
        exact (hSameHead v hv).symm
      have hOccE :
          (B.childBranch t.child).Occupied E :=
        ((B.childBranch t.child).occupied_congr_vertices C E hCE).mp
          t.occupied
      have hMsgC :
          branchMessage C (B.childBranch t.child) = some t.gain := by
        rw [branchMessage_eq_some_of_occupied C
          (B.childBranch t.child) t.occupied, t.gain_eq_F]
      have hMsgE :
          branchMessage E (B.childBranch t.child) = some t.gain := by
        calc
          branchMessage E (B.childBranch t.child) =
              branchMessage C (B.childBranch t.child) :=
            (branchMessage_congr_vertices C E
              (B.childBranch t.child) hCE).symm
          _ = some t.gain := hMsgC
      rcases hChildAttain t.child E t.gain (E B.root)
          hOccE hMsgE hSafe.1 with
        ⟨E₁, hClear₁, hRoot₁⟩
      rcases hClear₁ with ⟨hReachRaw, hCleared₁⟩
      have hStart :
          (B.childBranch t.child).withBoundary E (E B.root) = E := by
        have hSelf := (B.childBranch t.child).withBoundary_self E
        simpa [childBranch] using hSelf
      have hReachChild :
          (B.childBranch t.child).BranchReach E E₁ := by
        rw [hStart] at hReachRaw
        exact hReachRaw
      have hReachParent : B.BranchReach E E₁ :=
        BranchReach.of_child B t.child hReachChild
      have hParent₁ : E₁ B.parent = E B.parent :=
        BranchReach.eq_of_not_mem_carrier
          (B.childBranch t.child) hReachChild
          (B.parent_not_mem_childBranch_carrier t.child)
      have hSameTail :
          ∀ s ∈ ts, ∀ v ∈ (B.childBranch s.child).vertices,
            E₁ v = C v := by
        intro s hs v hv
        have hst : s.1 ≠ t.1 := by
          intro hEq
          have hObj : s = t := Subtype.ext hEq
          subst s
          exact htNot hs
        have hChildNe : s.child.vertex ≠ t.child.vertex := by
          simpa using hst
        have hOutside :
            v ∉ (B.childBranch t.child).carrier :=
          B.mem_childBranch_vertices_not_mem_sibling_carrier
            s.child t.child hChildNe hv
        have hEqStep :=
          BranchReach.eq_of_not_mem_carrier
            (B.childBranch t.child) hReachChild hOutside
        calc
          E₁ v = E v := hEqStep
          _ = C v := hSame s (by simp [hs]) v hv
      have hSafeTail :
          TaskScheduleSafe
            (fun s : B.OccupiedChild C => s.gain)
            (E₁ B.root : ℤ) ts := by
        rw [hRoot₁]
        exact hSafe.2
      rcases ih E₁ hNodupTail hSameTail hSafeTail with
        ⟨D, hReachTail, hRootTail, hParentTail,
          hClearedTail, hUntouchedTail⟩
      have hReachAll : B.BranchReach E D :=
        Relation.ReflTransGen.trans hReachParent hReachTail
      have hRootAll :
          (D B.root : ℤ) =
            (E B.root : ℤ) +
              taskGainSum
                (fun s : B.OccupiedChild C => s.gain) (t :: ts) := by
        rw [hRootTail, hRoot₁]
        simp only [taskGainSum]
        ring
      have hParentAll : D B.parent = E B.parent := by
        rw [hParentTail, hParent₁]
      have hHeadNotTail :
          ∀ s ∈ ts, s.1 ≠ t.child.vertex := by
        intro s hs hEq
        have hEq' : s.1 = t.1 := by
          simpa using hEq
        have hObj : s = t := Subtype.ext hEq'
        subst s
        exact htNot hs
      have hHeadPres :
          ∀ v ∈ (B.childBranch t.child).vertices, D v = E₁ v :=
        hUntouchedTail t.child hHeadNotTail
      have hClearedHead :
          (B.childBranch t.child).Cleared D := by
        intro v hv
        rw [hHeadPres v hv]
        exact hCleared₁ v hv
      have hClearedAll :
          ∀ s ∈ t :: ts, (B.childBranch s.child).Cleared D := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hClearedHead
        · exact hClearedTail s hs
      have hUntouchedAll :
          ∀ c : B.Child,
            (∀ s ∈ t :: ts, s.1 ≠ c.vertex) →
            ∀ v ∈ (B.childBranch c).vertices, D v = E v := by
        intro c hnot v hv
        have hnotHead : t.1 ≠ c.vertex :=
          hnot t (by simp)
        have hnotTail : ∀ s ∈ ts, s.1 ≠ c.vertex := by
          intro s hs
          exact hnot s (by simp [hs])
        have hcHead : c.vertex ≠ t.child.vertex := by
          simpa using hnotHead.symm
        have hOutside :
            v ∉ (B.childBranch t.child).carrier :=
          B.mem_childBranch_vertices_not_mem_sibling_carrier
            c t.child hcHead hv
        have hStep :=
          BranchReach.eq_of_not_mem_carrier
            (B.childBranch t.child) hReachChild hOutside
        calc
          D v = E₁ v := hUntouchedTail c hnotTail v hv
          _ = E v := hStep
      exact
        ⟨D, hReachAll, hRootAll, hParentAll,
          hClearedAll, hUntouchedAll⟩
end TreeStack.OrientedBranch
