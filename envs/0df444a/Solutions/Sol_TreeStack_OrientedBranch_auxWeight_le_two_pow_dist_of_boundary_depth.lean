-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxWeight_le_two_pow_dist_of_boundary_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:38:21.181792+00:00
-- url     : https://prove2.me/submissions/e1ab6175-8ccb-4fa0-9881-e2af0f7d2061

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
import Theorems.Thm_TreeStack_OrientedBranch_sourceFiber_dist_le_of_boundary_depth
import Theorems.Thm_TreeStack_OrientedBranch_auxWeight_eq_two_pow_dist_of_mem_sourceFiber

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    auxWeight C ambientRoot hScores v ≤
      2 ^ T.graph.dist r v := by
  rw [auxWeight_eq_two_pow_dist_of_mem_sourceFiber
    C ambientRoot hScores s v hv]
  exact Nat.pow_le_pow_right Nat.zero_lt_two
    (sourceFiber_dist_le_of_boundary_depth
      C ambientRoot hScores hrs ha hb hadj hDepth hv)
end TreeStack.OrientedBranch
