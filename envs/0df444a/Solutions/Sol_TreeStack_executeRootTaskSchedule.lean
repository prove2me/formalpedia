-- Prove2me | solution 1 for TreeStack.executeRootTaskSchedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:55:07.814029+00:00
-- url     : https://prove2.me/submissions/327e5381-ad2e-4eb5-8725-02ba66a6ed60

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_mem_incidentBranch_vertices_not_mem_sibling_carrier
import Theorems.Thm_TreeStack_RootTask_occupied
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_gain_eq_F
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_toReach
import Theorems.Thm_TreeStack_RootTask_mem_vertices_not_mem_sibling_carrier
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_eq_of_not_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_F
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_boundary_attainment
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_congr_vertices
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_occupied_congr_vertices
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.boundaryParityWeight_parent
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.mem_rootTasks

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    ∀ (tasks : List (RootTask T C r)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ t.branch.vertices, E v = C v) →
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (E r : ℤ) tasks →
      ∃ D : Configuration V,
        Reach T.graph E D ∧
        (D r : ℤ) =
          (E r : ℤ) +
            taskGainSum (fun t : RootTask T C r => t.gain) tasks ∧
        (∀ t ∈ tasks, t.branch.Cleared D) ∧
        (∀ (u : V) (h : T.graph.Adj u r),
          (∀ t ∈ tasks, t.1 ≠ u) →
          ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v) := by
  classical
  intro tasks
  induction tasks with
  | nil =>
      intro E hNodup hSame hSafe
      refine ⟨E, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp [taskGainSum]
      · intro t ht
        simp at ht
      · intro u h hnot v hv
        rfl
  | cons t ts ih =>
      intro E hNodup hSame hSafe
      have hNodupData := List.nodup_cons.mp hNodup
      have htNot : t ∉ ts := hNodupData.1
      have hNodupTail : ts.Nodup := hNodupData.2
      change
        0 < (E r : ℤ) + t.gain ∧
          TaskScheduleSafe
            (fun s : RootTask T C r => s.gain)
            ((E r : ℤ) + t.gain) ts at hSafe
      have hSameHead :
          ∀ v ∈ t.branch.vertices, E v = C v :=
        hSame t (by simp)
      have hCE :
          ∀ v ∈ t.branch.vertices, C v = E v := by
        intro v hv
        exact (hSameHead v hv).symm
      have hOccE : t.branch.Occupied E :=
        (t.branch.occupied_congr_vertices C E hCE).mp t.occupied
      have hMsgC :
          OrientedBranch.branchMessage C t.branch = some t.gain := by
        rw [OrientedBranch.branchMessage_eq_some_of_occupied
          C t.branch t.occupied, t.gain_eq_F]
      have hMsgE :
          OrientedBranch.branchMessage E t.branch = some t.gain := by
        calc
          OrientedBranch.branchMessage E t.branch =
              OrientedBranch.branchMessage C t.branch :=
            (OrientedBranch.branchMessage_congr_vertices
              C E t.branch hCE).symm
          _ = some t.gain := hMsgC
      rcases OrientedBranch.boundary_attainment
          E t.branch hOccE t.gain hMsgE (E r) hSafe.1 with
        ⟨E₁, hClear₁, hRoot₁⟩
      rcases hClear₁ with ⟨hReachRaw, hCleared₁⟩
      have hStart : t.branch.withBoundary E (E r) = E := by
        have hSelf := t.branch.withBoundary_self E
        simpa using hSelf
      have hReachBranch : t.branch.BranchReach E E₁ := by
        rw [hStart] at hReachRaw
        exact hReachRaw
      have hReachGlobal : Reach T.graph E E₁ :=
        OrientedBranch.BranchReach.toReach t.branch hReachBranch
      have hRoot₁' :
          (E₁ r : ℤ) = (E r : ℤ) + t.gain := by
        simpa using hRoot₁
      have hSameTail :
          ∀ s ∈ ts, ∀ v ∈ s.branch.vertices, E₁ v = C v := by
        intro s hs v hv
        have hst : s.1 ≠ t.1 := by
          intro hEq
          have hObj : s = t := Subtype.ext hEq
          subst s
          exact htNot hs
        have hOutside : v ∉ t.branch.carrier :=
          s.mem_vertices_not_mem_sibling_carrier t hst hv
        have hEqStep :=
          OrientedBranch.BranchReach.eq_of_not_mem_carrier
            t.branch hReachBranch hOutside
        calc
          E₁ v = E v := hEqStep
          _ = C v := hSame s (by simp [hs]) v hv
      have hSafeTail :
          TaskScheduleSafe
            (fun s : RootTask T C r => s.gain)
            (E₁ r : ℤ) ts := by
        rw [hRoot₁']
        exact hSafe.2
      rcases ih E₁ hNodupTail hSameTail hSafeTail with
        ⟨D, hReachTail, hRootTail, hClearedTail, hUntouchedTail⟩
      have hReachAll : Reach T.graph E D :=
        Relation.ReflTransGen.trans hReachGlobal hReachTail
      have hRootAll :
          (D r : ℤ) =
            (E r : ℤ) +
              taskGainSum
                (fun s : RootTask T C r => s.gain) (t :: ts) := by
        rw [hRootTail, hRoot₁']
        simp only [taskGainSum]
        ring
      have hHeadNotTail :
          ∀ s ∈ ts, s.1 ≠ t.1 := by
        intro s hs hEq
        have hObj : s = t := Subtype.ext hEq
        subst s
        exact htNot hs
      have hHeadPres :
          ∀ v ∈ t.branch.vertices, D v = E₁ v := by
        intro v hv
        have hv' :
            v ∈ (incidentBranch T r t.1 (Classical.choose t.2)).vertices := by
          simpa [RootTask.branch] using hv
        exact
          hUntouchedTail t.1 (Classical.choose t.2)
            hHeadNotTail v hv'
      have hClearedHead : t.branch.Cleared D := by
        intro v hv
        rw [hHeadPres v hv]
        exact hCleared₁ v hv
      have hClearedAll :
          ∀ s ∈ t :: ts, s.branch.Cleared D := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hClearedHead
        · exact hClearedTail s hs
      have hUntouchedAll :
          ∀ (u : V) (h : T.graph.Adj u r),
            (∀ s ∈ t :: ts, s.1 ≠ u) →
            ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v := by
        intro u h hnot v hv
        have hnotHead : t.1 ≠ u :=
          hnot t (by simp)
        have hnotTail : ∀ s ∈ ts, s.1 ≠ u := by
          intro s hs
          exact hnot s (by simp [hs])
        have hOutside : v ∉ t.branch.carrier := by
          change
            v ∉ (incidentBranch T r t.1 (Classical.choose t.2)).carrier
          exact mem_incidentBranch_vertices_not_mem_sibling_carrier
            (T := T) r h (Classical.choose t.2) hnotHead.symm hv
        have hStep :=
          OrientedBranch.BranchReach.eq_of_not_mem_carrier
            t.branch hReachBranch hOutside
        calc
          D v = E₁ v := hUntouchedTail u h hnotTail v hv
          _ = E v := hStep
      exact ⟨D, hReachAll, hRootAll, hClearedAll, hUntouchedAll⟩
end TreeStack
