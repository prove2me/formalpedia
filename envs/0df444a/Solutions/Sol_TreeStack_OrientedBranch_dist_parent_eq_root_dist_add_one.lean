-- Prove2me | solution 1 for TreeStack.OrientedBranch.dist_parent_eq_root_dist_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:00:27.484853+00:00
-- url     : https://prove2.me/submissions/9a38b396-2f97-4a21-8bc0-caf9806432a7

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_OrientedBranch_tree_path_length_eq_dist
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
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
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
theorem _root_.solution
    (B : OrientedBranch T) {x : V} (hx : x ∈ B.vertices) :
    T.graph.dist B.parent x =
      T.graph.dist B.root x + 1 := by
  classical
  have hrComp :
      B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hreach :
      B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrComp hxComp
  obtain ⟨p₀, hp₀⟩ := hreach.exists_isPath
  have hle : B.deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let p : T.graph.Walk B.root x := p₀.mapLe hle
  have hp : p.IsPath := hp₀.mapLe hle
  have hparentNot : B.parent ∉ p.support := by
    intro hparent
    have hparent₀ : B.parent ∈ p₀.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hparent
    let q₀ := p₀.takeUntil B.parent hparent₀
    have hparentMem : B.parent ∈ B.vertices := by
      rw [vertices, Set.mem_toFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff, component]
      exact
        (SimpleGraph.ConnectedComponent.sound q₀.reachable).symm
    exact B.parent_not_mem_vertices hparentMem
  let q : T.graph.Walk B.parent x := p.cons B.adj.symm
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hp, hparentNot⟩
  have hpdist := tree_path_length_eq_dist (T := T) p hp
  have hqdist := tree_path_length_eq_dist (T := T) q hq
  simpa [q, p, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_mapLe, hpdist] using hqdist.symm
end TreeStack.OrientedBranch
