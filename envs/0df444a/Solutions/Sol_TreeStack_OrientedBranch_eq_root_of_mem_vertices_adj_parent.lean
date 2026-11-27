-- Prove2me | solution 1 for TreeStack.OrientedBranch.eq_root_of_mem_vertices_adj_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:51.669905+00:00
-- url     : https://prove2.me/submissions/b8e67f0d-f40b-4af8-b6f2-9bfc9d23b9da

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_edge_leaving_vertices_eq_boundary
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.OrientedBranch.root_ne_parent

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T)
    {u : V} (hu : u ∈ B.vertices) (hup : T.graph.Adj u B.parent) :
    u = B.root := by
  have hEdge :=
    B.edge_leaving_vertices_eq_boundary hu B.parent_not_mem_vertices hup
  rw [Sym2.eq_iff] at hEdge
  rcases hEdge with h | h
  · exact h.1
  · exact (B.root_ne_parent h.2.symm).elim
end TreeStack.OrientedBranch
