-- Prove2me | solution 1 for TreeStack.OrientedBranch.two_mul_auxWeightInt_le_of_auxArrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:12:48.447324+00:00
-- url     : https://prove2.me/submissions/24288b0a-3e70-4385-9a8b-ea668b589d48

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
import Theorems.Thm_TreeStack_OrientedBranch_two_mul_auxWeight_le_of_auxArrow

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeightInt C ambientRoot hScores u ≤
      auxWeightInt C ambientRoot hScores v := by
  change
    (2 : ℤ) * (auxWeight C ambientRoot hScores u : ℤ) ≤
      (auxWeight C ambientRoot hScores v : ℤ)
  exact_mod_cast
    (two_mul_auxWeight_le_of_auxArrow
      C ambientRoot hScores hArrow)
end TreeStack.OrientedBranch
