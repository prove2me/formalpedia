-- Prove2me | solution 1 for TreeStack.OrientedBranch.obstruction_scores_zero_on_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:02:06.493393+00:00
-- url     : https://prove2.me/submissions/dcf19c97-6a0e-41f4-ba7e-90b97d3ebee6

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_OrientedBranch_obstruction_score_root_of_parent_score_zero
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_vertices_subset
import Theorems.Thm_TreeStack_OrientedBranch_exists_childBranch_mem_of_mem_vertices_ne_root


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    ∀ x ∈ B.vertices,
      score T (obstruction T r) x = 0 := by
  classical
  have hRoot :
      score T (obstruction T r) B.root = 0 :=
    B.obstruction_score_root_of_parent_score_zero r hAway hParent
  intro x hx
  by_cases hxr : x = B.root
  · subst x
    exact hRoot
  · rcases
      B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, hxc⟩
    have hAwayChild :
        r ∉ (B.childBranch c).vertices := by
      intro hr
      exact hAway (B.childBranch_vertices_subset c hr)
    exact
      solution
        r (B.childBranch c) hAwayChild hRoot x hxc
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt _
end TreeStack.OrientedBranch
