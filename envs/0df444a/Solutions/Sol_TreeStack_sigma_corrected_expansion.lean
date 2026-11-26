-- Prove2me | solution 1 for TreeStack.sigma_corrected_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:27.861254+00:00
-- url     : https://prove2.me/submissions/4db2d104-220c-4ec2-87cc-646324e5db91

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
import Theorems.Thm_TreeStack_sigmaVertices_eq_insert
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigma T r =
      1 + T.graph.degree r +
        ∑ v ∈ nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by
  rw [sigma, sigmaVertices_eq_insert]
  have hnot : r ∉ nonRootInternalVertices T r := by
    simp [nonRootInternalVertices]
  rw [Finset.sum_insert hnot]
  simp [Nat.add_assoc]
end TreeStack
