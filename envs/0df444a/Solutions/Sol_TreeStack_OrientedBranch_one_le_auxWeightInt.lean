-- Prove2me | solution 1 for TreeStack.OrientedBranch.one_le_auxWeightInt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:16:40.295199+00:00
-- url     : https://prove2.me/submissions/60ae10d6-7c63-4835-9f6d-0e31ba02e319

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
import Theorems.Thm_TreeStack_OrientedBranch_auxWeight_pos


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    1 ≤ auxWeightInt C ambientRoot hScores v := by
  have hpos : 0 < auxWeight C ambientRoot hScores v :=
    auxWeight_pos C ambientRoot hScores v
  have hone : 1 ≤ auxWeight C ambientRoot hScores v := by
    omega
  change (1 : ℤ) ≤ (auxWeight C ambientRoot hScores v : ℤ)
  exact Int.ofNat_le.mpr hone
end TreeStack.OrientedBranch
