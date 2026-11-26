-- Prove2me | solution 1 for TreeStack.sigmaVertices_eq_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:28.481055+00:00
-- url     : https://prove2.me/submissions/4722b845-d4fc-4f58-a462-b5eaf13d3e81

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
    sigmaVertices T r = insert r (nonRootInternalVertices T r) := by
  ext v
  by_cases hvr : v = r
  · simp [sigmaVertices, nonRootInternalVertices, hvr]
  · simp [sigmaVertices, nonRootInternalVertices, hvr]
end TreeStack
