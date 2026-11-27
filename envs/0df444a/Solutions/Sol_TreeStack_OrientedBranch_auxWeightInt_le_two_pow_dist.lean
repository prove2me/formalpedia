-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxWeightInt_le_two_pow_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:21.194794+00:00
-- url     : https://prove2.me/submissions/5dac35d7-41a4-4aba-9bc3-118b3e310322

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hHeight :
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxWeightInt C ambientRoot hScores v ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by
  change
    (auxWeight C ambientRoot hScores v : ℤ) ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ)
  exact_mod_cast
    Nat.pow_le_pow_right Nat.zero_lt_two hHeight
end TreeStack.OrientedBranch
