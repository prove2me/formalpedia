-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxSourceFiber_treePathConnected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:56.570442+00:00
-- url     : https://prove2.me/submissions/dca84fde-63fa-4761-a78c-15e1ded2d3ef

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
import Theorems.Thm_TreeStack_OrientedBranch_exists_path_within_auxSourceFiber

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V) :
    TreePathConnected (T := T)
      (auxSourceFiber C ambientRoot hScores r) := by
  intro x y hx hy
  exact exists_path_within_auxSourceFiber
    C ambientRoot hScores r x y hx hy
end TreeStack.OrientedBranch
