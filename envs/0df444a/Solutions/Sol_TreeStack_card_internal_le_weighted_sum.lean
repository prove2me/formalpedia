-- Prove2me | solution 1 for TreeStack.card_internal_le_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:38.852901+00:00
-- url     : https://prove2.me/submissions/abfbb2e4-48c2-40fa-8862-af54cff858db

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
    (nonRootInternalVertices T r).card ≤
      ∑ v ∈ nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by
  calc
    (nonRootInternalVertices T r).card =
        ∑ _v ∈ nonRootInternalVertices T r, 1 := by simp
    _ ≤ ∑ v ∈ nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by
      exact Finset.sum_le_sum fun v hv => by
        have hv' : v ≠ r ∧ 1 < T.graph.degree v := by
          simpa [nonRootInternalVertices] using hv
        have hprod :
            0 < T.graph.degree v * 2 ^ T.graph.dist r v := by
          exact Nat.mul_pos (by omega) (by positivity)
        omega
end TreeStack
