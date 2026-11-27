-- Prove2me | solution 1 for TreeStack.OrientedBranch.sum_dite_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:58:03.301989+00:00
-- url     : https://prove2.me/submissions/cb3e7946-3603-4dfa-8012-bb6be9bfdec3

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_Child_eq_of_vertex_eq
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_rootTasks
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
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_rootTasks
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution {M : Type*} [AddCommMonoid M]
    (B : OrientedBranch T) (f : B.Child → M) :
    (∑ v : V,
      if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
        f { vertex := v, adj := h.1, ne_parent := h.2 }
      else
        0) =
      ∑ c : B.Child, f c := by
  classical
  let term : V → M := fun v =>
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      f { vertex := v, adj := h.1, ne_parent := h.2 }
    else
      0
  have hrestrict :
      (∑ v ∈ B.childFinset, term v) =
        ∑ v : V, term v := by
    apply Finset.sum_subset (Finset.subset_univ B.childFinset)
    intro v hvUniv hvNot
    have hnot :
        ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
      intro h
      exact hvNot ((B.mem_childFinset v).2 h)
    simp [term, hnot]
  rw [← hrestrict]
  change
    (∑ v ∈ B.childFinset, term v) =
      ∑ c ∈ (Finset.univ : Finset B.Child), f c
  apply Finset.sum_bij
    (fun v hv =>
      { vertex := v
        adj := ((B.mem_childFinset v).1 hv).1
        ne_parent := ((B.mem_childFinset v).1 hv).2 })
  · intro v hv
    exact Finset.mem_univ _
  · intro v₁ hv₁ v₂ hv₂ hEq
    exact congrArg Child.vertex hEq
  · intro c hc
    refine ⟨c.vertex, ?_, ?_⟩
    · exact (B.mem_childFinset c.vertex).2 ⟨c.adj, c.ne_parent⟩
    · apply Child.eq_of_vertex_eq
      rfl
  · intro v hv
    have h := (B.mem_childFinset v).1 hv
    simp [term, h]
end TreeStack.OrientedBranch
