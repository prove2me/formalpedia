-- Prove2me | solution 1 for TreeStack.OrientedBranch.configurationSlackTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:19.979088+00:00
-- url     : https://prove2.me/submissions/e003fb76-4e63-443c-85d9-6778f5763c96

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
import Theorems.Thm_TreeStack_OrientedBranch_one_le_auxWeightInt

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    0 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
  exact mul_nonneg
    (sub_nonneg.mpr (one_le_auxWeightInt C ambientRoot hScores v))
    (by positivity)
end TreeStack.OrientedBranch
