-- Prove2me | solution 1 for TreeStack.exists_incidentBranch_mem_of_ne_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:41:25.826795+00:00
-- url     : https://prove2.me/submissions/127cb857-bac1-481b-a944-b7dd83201849

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
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

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (r : V) {x : V} (hxr : x ≠ r) :
    ∃ u : V, ∃ h : T.graph.Adj u r,
      x ∈ (incidentBranch T r u h).vertices := by
  classical
  obtain ⟨p, hp⟩ :=
    T.isTree.connected.preconnected.exists_isPath r x
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hxr.symm p with
    ⟨u, hru, p', hpEq⟩
  rw [hpEq] at hp
  have hpData :=
    (SimpleGraph.Walk.cons_isPath_iff hru p').mp hp
  have hrNot : r ∉ p'.support := hpData.2
  have hur : T.graph.Adj u r := hru.symm
  have havoid : s(u, r) ∉ p'.edges := by
    intro he
    exact hrNot (p'.snd_mem_support_of_mem_edges he)
  let q :
      (T.graph.deleteEdges {s(u, r)}).Walk u x :=
    p'.toDeleteEdges {s(u, r)} (by
      intro e he
      simp only [Set.mem_singleton_iff]
      intro heq
      subst e
      exact havoid he)
  have hreach :
      (incidentBranch T r u hur).deletedGraph.Reachable u x := by
    change (T.graph.deleteEdges {s(u, r)}).Reachable u x
    exact ⟨q⟩
  refine ⟨u, hur, ?_⟩
  rw [OrientedBranch.vertices, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff,
    OrientedBranch.component]
  exact (SimpleGraph.ConnectedComponent.sound hreach).symm
end TreeStack
