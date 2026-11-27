-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxInternalDegreePotential_le_rootedInternalPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:11.605064+00:00
-- url     : https://prove2.me/submissions/bee9f562-529f-41ea-bd26-e599bcf6f5c2

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
import Theorems.Thm_TreeStack_OrientedBranch_auxWeightInt_le_two_pow_dist

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hHeight : ∀ v,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxInternalDegreePotential C ambientRoot hScores ≤
      (rootedInternalPotential T r : ℤ) := by
  unfold auxInternalDegreePotential rootedInternalPotential
  calc
    (∑ v ∈ ambientInternalVertices (T := T),
        (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v) ≤
      ∑ v ∈ ambientInternalVertices (T := T),
        (T.graph.degree v : ℤ) *
          ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by
      exact Finset.sum_le_sum fun v _ => by
        exact mul_le_mul_of_nonneg_left
          (auxWeightInt_le_two_pow_dist
            C ambientRoot hScores r v (hHeight v))
          (by positivity)
    _ = (∑ v ∈ ambientInternalVertices (T := T),
          T.graph.degree v * 2 ^ T.graph.dist r v : ℕ) := by
      norm_cast
end TreeStack.OrientedBranch
