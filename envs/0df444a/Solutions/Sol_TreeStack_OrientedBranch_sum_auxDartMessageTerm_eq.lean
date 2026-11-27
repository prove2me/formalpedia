-- Prove2me | solution 1 for TreeStack.OrientedBranch.sum_auxDartMessageTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:38.581347+00:00
-- url     : https://prove2.me/submissions/c08da6e7-d9eb-406d-b4b2-35f0cf0d8865

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
import Theorems.Thm_TreeStack_OrientedBranch_sum_neighbor_rootMessageTerm_eq

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ d : T.graph.Dart,
      auxDartMessageTerm C ambientRoot hScores d) =
      ∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by
  calc
    (∑ d : T.graph.Dart,
        auxDartMessageTerm C ambientRoot hScores d) =
        ∑ p : Σ v : V, T.graph.neighborSet v,
          auxDartMessageTerm C ambientRoot hScores
            ((dartEquivHeadNeighbor (T := T)).symm p) := by
      exact
        (Equiv.sum_comp (dartEquivHeadNeighbor (T := T)).symm
          (auxDartMessageTerm C ambientRoot hScores)).symm
    _ = ∑ v : V,
          ∑ u : T.graph.neighborSet v,
            auxWeightInt C ambientRoot hScores v *
              rootMessageTerm T C v u := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ v : V,
          auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by
      apply Fintype.sum_congr
      intro v
      rw [← Finset.mul_sum, sum_neighbor_rootMessageTerm_eq]
end TreeStack.OrientedBranch
