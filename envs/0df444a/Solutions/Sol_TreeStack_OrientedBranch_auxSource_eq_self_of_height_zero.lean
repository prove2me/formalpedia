-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxSource_eq_self_of_height_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:17:27.039148+00:00
-- url     : https://prove2.me/submissions/0c31d6ff-34cb-4c66-a71d-7ca6fe1e1a2a

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_eq_of_height_zero

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSource C ambientRoot hScores v = v := by
  unfold auxSource
  rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]
end TreeStack.OrientedBranch
