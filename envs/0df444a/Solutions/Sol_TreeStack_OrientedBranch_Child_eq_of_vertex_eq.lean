-- Prove2me | solution 1 for TreeStack.OrientedBranch.Child.eq_of_vertex_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:23.926018+00:00
-- url     : https://prove2.me/submissions/e3ab94af-5a32-41cd-9561-68f5ce448c5b

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
namespace Child
theorem _root_.solution {B : OrientedBranch T} {c d : B.Child}
    (h : c.vertex = d.vertex) : c = d := by
  cases c with
  | mk cv ca cn =>
      cases d with
      | mk dv da dn =>
          simp only at h
          subst dv
          rfl
end Child
end TreeStack.OrientedBranch
