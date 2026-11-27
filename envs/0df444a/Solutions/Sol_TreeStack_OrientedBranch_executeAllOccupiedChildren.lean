-- Prove2me | solution 1 for TreeStack.OrientedBranch.executeAllOccupiedChildren
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:43:58.036895+00:00
-- url     : https://prove2.me/submissions/3a04b333-eee4-4d93-91b7-f58413011dc1

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_taskGainSum_orderedTasks
import Theorems.Thm_TreeStack_mem_orderedTasks_iff
import Theorems.Thm_TreeStack_orderedTasks_nodup
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_occupiedChildTasks_nodup
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_taskGainSum_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_executeOccupiedTaskSchedule
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_Child_eq_of_vertex_eq
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
import Theorems.Thm_TreeStack_OrientedBranch_exists_childBranch_mem_of_mem_vertices_ne_root
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

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (B : OrientedBranch T) (C E : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E' : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E' →
        branchMessage E' (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E' q D ∧
            (D B.root : ℤ) = (q : ℤ) + d)
    (hSame :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = C v)
    (hSafe :
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ)
        (orderedTasks
          (fun t : B.OccupiedChild C => t.gain)
          (B.occupiedChildTasks C))) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B ∧
      D B.parent = E B.parent ∧
      (∀ v ∈ B.vertices, v ≠ B.root → D v = 0) := by
  classical
  let gain : B.OccupiedChild C → ℤ := fun t => t.gain
  let baseTasks : List (B.OccupiedChild C) := B.occupiedChildTasks C
  let scheduled : List (B.OccupiedChild C) :=
    orderedTasks gain baseTasks
  have hNodupBase : baseTasks.Nodup := by
    simpa [baseTasks] using B.occupiedChildTasks_nodup C
  have hNodupScheduled : scheduled.Nodup := by
    exact orderedTasks_nodup gain hNodupBase
  have hSameScheduled :
      ∀ t ∈ scheduled, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v := by
    intro t ht v hv
    have hvB : v ∈ B.vertices :=
      B.childBranch_vertices_subset t.child hv
    have hvRoot : v ≠ B.root := by
      intro hvr
      subst v
      exact (B.childBranch t.child).parent_not_mem_vertices
        (by simpa using hv)
    exact hSame v hvB hvRoot
  have hSafe' :
      TaskScheduleSafe gain (E B.root : ℤ) scheduled := by
    simpa [gain, baseTasks, scheduled] using hSafe
  rcases executeOccupiedTaskSchedule B C hChildAttain
      scheduled E hNodupScheduled hSameScheduled hSafe' with
    ⟨D, hReach, hRoot, hParent, hCleared, hUntouched⟩
  have hRoot' :
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B := by
    calc
      (D B.root : ℤ) =
          (E B.root : ℤ) + taskGainSum gain scheduled := hRoot
      _ =
          (E B.root : ℤ) + taskGainSum gain baseTasks := by
            change
              (E B.root : ℤ) +
                  taskGainSum gain (orderedTasks gain baseTasks) =
                (E B.root : ℤ) + taskGainSum gain baseTasks
            rw [taskGainSum_orderedTasks]
      _ = (E B.root : ℤ) + childMessageSum C B := by
            change
              (E B.root : ℤ) +
                  taskGainSum
                    (fun t : B.OccupiedChild C => t.gain)
                    (B.occupiedChildTasks C) =
                (E B.root : ℤ) + childMessageSum C B
            rw [taskGainSum_occupiedChildTasks]
  have hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → D v = 0 := by
    intro v hvB hvRoot
    rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hvB hvRoot with
      ⟨c, hvc⟩
    by_cases hOcc : (B.childBranch c).Occupied C
    · let hcv : B.IsChildVertex c.vertex := ⟨c.adj, c.ne_parent⟩
      have hcEq : B.childOfVertex c.vertex hcv = c :=
        Child.eq_of_vertex_eq rfl
      let t : B.OccupiedChild C :=
        ⟨c.vertex, ⟨hcv, by
          rw [hcEq]
          exact hOcc⟩⟩
      have htChild : t.child = c := by
        apply Child.eq_of_vertex_eq
        calc
          t.child.vertex = t.1 := t.child_vertex
          _ = c.vertex := rfl
      have htBase : t ∈ baseTasks := by
        simpa [baseTasks] using B.mem_occupiedChildTasks C t
      have htScheduled : t ∈ scheduled := by
        change t ∈ orderedTasks gain baseTasks
        exact (mem_orderedTasks_iff gain baseTasks t).2 htBase
      have htClear := hCleared t htScheduled
      rw [htChild] at htClear
      exact htClear v hvc
    · have hNoTask :
          ∀ t ∈ scheduled, t.1 ≠ c.vertex := by
        intro t ht hEq
        have htc : t.child = c := by
          apply Child.eq_of_vertex_eq
          simpa using hEq
        have htOcc := t.occupied
        rw [htc] at htOcc
        exact hOcc htOcc
      have hPres : D v = E v :=
        hUntouched c hNoTask v hvc
      have hEC : E v = C v :=
        hSame v hvB hvRoot
      have hC0 : C v = 0 := by
        by_contra hne
        exact hOcc ⟨v, hvc, Nat.pos_of_ne_zero hne⟩
      calc
        D v = E v := hPres
        _ = C v := hEC
        _ = 0 := hC0
  exact ⟨D, hReach, hRoot', hParent, hNonroot⟩
end TreeStack.OrientedBranch
