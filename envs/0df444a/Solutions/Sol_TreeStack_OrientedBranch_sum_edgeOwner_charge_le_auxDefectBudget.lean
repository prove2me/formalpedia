-- Prove2me | solution 1 for TreeStack.OrientedBranch.sum_edgeOwner_charge_le_auxDefectBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:49.123442+00:00
-- url     : https://prove2.me/submissions/9092ba79-2064-4d29-b1ff-689a55200ea1

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
import Theorems.Thm_TreeStack_OrientedBranch_edgeOwner_injective
import Theorems.Thm_TreeStack_OrientedBranch_auxWeightInt_nonneg
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
attribute [local simp] TreeStack.scoreDefect_nonneg_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
        scoreDefect T C (edgeOwner ambientRoot e)) ≤
      auxDefectBudget C ambientRoot hScores := by
  let f : V → ℤ := fun v =>
    auxWeightInt C ambientRoot hScores v * scoreDefect T C v
  have hf : ∀ v, 0 ≤ f v := by
    intro v
    exact mul_nonneg
      (auxWeightInt_nonneg C ambientRoot hScores v)
      ((scoreDefect_nonneg_iff T C v).2 (hScores v))
  let owner : T.graph.edgeFinset → V := edgeOwner ambientRoot
  have hOwner : Function.Injective owner :=
    edgeOwner_injective (T := T) ambientRoot
  calc
    (∑ e : T.graph.edgeFinset,
        auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
          scoreDefect T C (edgeOwner ambientRoot e)) =
        ∑ e : T.graph.edgeFinset, f (owner e) := by rfl
    _ = ∑ v ∈ (Finset.univ : Finset T.graph.edgeFinset).image owner, f v := by
      rw [Finset.sum_image]
      intro e _ g _ heg
      exact hOwner heg
    _ ≤ ∑ v : V, f v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
        (fun v _ _ => hf v)
    _ = auxDefectBudget C ambientRoot hScores := by
      rfl
end TreeStack.OrientedBranch
