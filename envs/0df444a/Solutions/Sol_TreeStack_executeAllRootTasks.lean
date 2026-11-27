-- Prove2me | solution 1 for TreeStack.executeAllRootTasks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:57:44.808193+00:00
-- url     : https://prove2.me/submissions/8e984f29-1ea0-434a-a73d-524c3b676022

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_exists_incidentBranch_mem_of_ne_root
import Theorems.Thm_TreeStack_RootTask_occupied
import Theorems.Thm_TreeStack_RootTask_branch_eq_incident
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_rootTasks_nodup
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_taskGainSum_rootTasks
import Theorems.Thm_TreeStack_executeRootTaskSchedule
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_not_occupied_iff_zero_on_vertices
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_orderedTasks_iff
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_orderedTasks_nodup
import Theorems.Thm_TreeStack_taskGainSum_orderedTasks
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
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSafe :
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (C r : ℤ)
        (orderedTasks
          (fun t : RootTask T C r => t.gain)
          (rootTasks T C r))) :
    ∃ D : Configuration V,
      Reach T.graph C D ∧
      (D r : ℤ) = score T C r ∧
      (∀ v : V, v ≠ r → D v = 0) := by
  classical
  let gain : RootTask T C r → ℤ := fun t => t.gain
  let baseTasks : List (RootTask T C r) := rootTasks T C r
  let scheduled : List (RootTask T C r) :=
    orderedTasks gain baseTasks
  have hNodupBase : baseTasks.Nodup := by
    simpa [baseTasks] using rootTasks_nodup T C r
  have hNodupScheduled : scheduled.Nodup :=
    orderedTasks_nodup gain hNodupBase
  have hSame :
      ∀ t ∈ scheduled, ∀ v ∈ t.branch.vertices, C v = C v := by
    intro t ht v hv
    rfl
  have hSafe' :
      TaskScheduleSafe gain (C r : ℤ) scheduled := by
    simpa [gain, baseTasks, scheduled] using hSafe
  rcases executeRootTaskSchedule T C r
      scheduled C hNodupScheduled hSame hSafe' with
    ⟨D, hReach, hRoot, hCleared, hUntouched⟩
  have hRootScore : (D r : ℤ) = score T C r := by
    calc
      (D r : ℤ) =
          (C r : ℤ) + taskGainSum gain scheduled := hRoot
      _ = (C r : ℤ) + taskGainSum gain baseTasks := by
            change
              (C r : ℤ) +
                  taskGainSum gain (orderedTasks gain baseTasks) =
                (C r : ℤ) + taskGainSum gain baseTasks
            rw [taskGainSum_orderedTasks]
      _ = (C r : ℤ) + rootMessageSum T C r := by
            change
              (C r : ℤ) +
                  taskGainSum
                    (fun t : RootTask T C r => t.gain)
                    (rootTasks T C r) =
                (C r : ℤ) + rootMessageSum T C r
            rw [taskGainSum_rootTasks]
      _ = score T C r := rfl
  have hOffRoot : ∀ v : V, v ≠ r → D v = 0 := by
    intro v hvr
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hvr with
      ⟨u, h, hv⟩
    by_cases hOcc : (incidentBranch T r u h).Occupied C
    · let t : RootTask T C r := ⟨u, ⟨h, hOcc⟩⟩
      have htBase : t ∈ baseTasks := by
        simpa [baseTasks] using mem_rootTasks T C r t
      have htScheduled : t ∈ scheduled := by
        change t ∈ orderedTasks gain baseTasks
        exact (mem_orderedTasks_iff gain baseTasks t).2 htBase
      have htBranch :
          t.branch = incidentBranch T r u h := by
        exact t.branch_eq_incident h
      have htClear := hCleared t htScheduled
      rw [htBranch] at htClear
      exact htClear v hv
    · have hNoTask :
          ∀ t ∈ scheduled, t.1 ≠ u := by
        intro t ht hEq
        have htOcc := t.occupied
        have htBranch :
            t.branch = incidentBranch T r u h := by
          subst u
          exact t.branch_eq_incident h
        rw [htBranch] at htOcc
        exact hOcc htOcc
      have hPres : D v = C v :=
        hUntouched u h hNoTask v hv
      have hC0 : C v = 0 := by
        exact
          ((incidentBranch T r u h).not_occupied_iff_zero_on_vertices C).1
            hOcc v hv
      exact hPres.trans hC0
  exact ⟨D, hReach, hRootScore, hOffRoot⟩
end TreeStack
