-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxHeight_eq_dist_auxSource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:33:52.634095+00:00
-- url     : https://prove2.me/submissions/628867e2-8917-44d8-8d73-51263f61b5b4

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_isPath
import Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_length
import Theorems.Thm_TreeStack_OrientedBranch_tree_path_length_eq_dist


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
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v := by
  have hPath :=
    auxSourceWalk_isPath C ambientRoot hScores v
  have hDist :=
    tree_path_length_eq_dist
      (T := T) (auxSourceWalk C ambientRoot hScores v).2 hPath
  have hLen :=
    auxSourceWalk_length C ambientRoot hScores v
  change
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v
  calc
    auxHeight C ambientRoot hScores v =
        (auxSourceWalk C ambientRoot hScores v).2.length := hLen.symm
    _ = T.graph.dist v (auxSource C ambientRoot hScores v) := hDist
    _ = T.graph.dist (auxSource C ambientRoot hScores v) v :=
      T.graph.dist_comm
end TreeStack.OrientedBranch
