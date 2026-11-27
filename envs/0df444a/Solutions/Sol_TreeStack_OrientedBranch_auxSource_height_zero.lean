-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxSource_height_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:07.219876+00:00
-- url     : https://prove2.me/submissions/79097f56-e84e-4e66-8796-96a68353b943

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
import Theorems.Thm_TreeStack_OrientedBranch_auxSource_eq_self_of_height_zero
import Theorems.Thm_TreeStack_OrientedBranch_auxSource_auxParent_of_pos

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores
      (auxSource C ambientRoot hScores v) = 0 := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSource_eq_self_of_height_zero
      C ambientRoot hScores v hZero]
    exact hZero
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    have hSource :=
      auxSource_auxParent_of_pos
        C ambientRoot hScores v hPos
    rw [← hSource]
    exact
      solution C ambientRoot hScores
        (auxParent C ambientRoot hScores v)
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega
end TreeStack.OrientedBranch
