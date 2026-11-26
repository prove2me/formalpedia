-- Prove2me | solution 1 for TreeStack.erase_root_eq_leaf_union_internal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:37.683456+00:00
-- url     : https://prove2.me/submissions/31a9e74f-0c20-4813-af9f-a702caad891e

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
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    (Finset.univ : Finset V).erase r =
      leafVertices T r ∪ nonRootInternalVertices T r := by
  ext v
  by_cases hvr : v = r
  · simp [leafVertices, nonRootInternalVertices, hvr]
  · have hv := hdeg v
    simp [leafVertices, nonRootInternalVertices, hvr]
    omega
end TreeStack
