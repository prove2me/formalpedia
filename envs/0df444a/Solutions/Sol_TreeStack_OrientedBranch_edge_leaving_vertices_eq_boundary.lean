-- Prove2me | solution 1 for TreeStack.OrientedBranch.edge_leaving_vertices_eq_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:24.67581+00:00
-- url     : https://prove2.me/submissions/4b8bf5ff-4fb7-488b-9b1b-9dab5806061a

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T)
    {u v : V} (hu : u ∈ B.vertices) (hv : v ∉ B.vertices)
    (huv : T.graph.Adj u v) :
    s(u, v) = s(B.root, B.parent) := by
  classical
  by_contra hne
  have hu' : u ∈ B.component.supp := by
    simpa [vertices] using hu
  have hadjDeleted : B.deletedGraph.Adj u v := by
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    exact ⟨huv, by simpa using hne⟩
  have hv' : v ∈ B.component.supp :=
    B.component.mem_supp_of_adj_mem_supp hu' hadjDeleted
  exact hv (by simpa [vertices] using hv')
end TreeStack.OrientedBranch
