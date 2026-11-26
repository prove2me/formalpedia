-- Prove2me | solution 1 for TreeStack.OrientedBranch.parent_not_mem_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:54.455686+00:00
-- url     : https://prove2.me/submissions/f786b150-58a5-4e09-845e-450a2c54db8e

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    B.parent ∉ B.vertices := by
  classical
  intro hp
  have hp' : B.parent ∈ B.component.supp := by
    rw [vertices, Set.mem_toFinset] at hp
    exact hp
  have hr' : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : B.deletedGraph.Reachable B.root B.parent :=
    B.component.reachable_of_mem_supp hr' hp'
  have hbridge : T.graph.IsBridge s(B.root, B.parent) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) B.adj
  have hnot :
      ¬ (T.graph.deleteEdges {s(B.root, B.parent)}).Reachable B.root B.parent :=
    SimpleGraph.isBridge_iff.mp hbridge
  exact hnot (by simpa [deletedGraph] using hreach)
end TreeStack.OrientedBranch
