-- Prove2me | solution 1 for TreeStack.leafVertices_disjoint_internal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:38.277999+00:00
-- url     : https://prove2.me/submissions/a09a39b9-945f-4c9d-a32c-6dee41369016

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    Disjoint (leafVertices T r) (nonRootInternalVertices T r) := by
  rw [Finset.disjoint_left]
  intro v hleaf hint
  simp only [leafVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hleaf
  simp only [nonRootInternalVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hint
  omega
end TreeStack
