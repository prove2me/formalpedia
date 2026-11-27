-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxSource_auxParent_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:04.273718+00:00
-- url     : https://prove2.me/submissions/bce60dab-76c6-41ea-b4c2-65b7067e2fef

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_eq_of_height_pos

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSource C ambientRoot hScores
        (auxParent C ambientRoot hScores v) =
      auxSource C ambientRoot hScores v := by
  unfold auxSource
  rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]
end TreeStack.OrientedBranch
