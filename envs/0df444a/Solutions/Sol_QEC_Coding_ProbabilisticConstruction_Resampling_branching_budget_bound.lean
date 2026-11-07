-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.branching_budget_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:12.397765+00:00
-- url     : https://prove2.me/submissions/7d50aa2a-f839-4d5e-8275-a15fa69bf89d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_resamplingBudget_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_one_add_budget_mul
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (p x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, p i ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) (i : I) :
    p i * ∏ j ∈ closedNeighbors G i, (1 + resamplingBudget x j) ≤
      resamplingBudget x i := by
  have hnn : ∀ j, 0 ≤ 1 + resamplingBudget x j := fun j =>
    add_nonneg (by norm_num) (resamplingBudget_nonneg x hx0 hx1 j)
  have hcancel : (∏ j ∈ G.neighborFinset i, (1 - x j)) *
      (∏ j ∈ G.neighborFinset i, (1 + resamplingBudget x j)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j hj
    simpa [mul_comm] using one_add_budget_mul x hx1 j
  have hi : i ∉ G.neighborFinset i := by simp
  have heq : (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) *
      (∏ j ∈ closedNeighbors G i, (1 + resamplingBudget x j)) =
      resamplingBudget x i := by
    rw [closedNeighbors, Finset.prod_insert hi]
    calc
      (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) *
          ((1 + resamplingBudget x i) *
            ∏ j ∈ G.neighborFinset i, (1 + resamplingBudget x j)) =
          (x i * (1 + resamplingBudget x i)) *
            ((∏ j ∈ G.neighborFinset i, (1 - x j)) *
              ∏ j ∈ G.neighborFinset i, (1 + resamplingBudget x j)) := by ring
      _ = resamplingBudget x i := by
        rw [hcancel, mul_one]
        unfold resamplingBudget
        field_simp [(sub_pos.mpr (hx1 i)).ne']
        ring
  exact heq ▸ mul_le_mul_of_nonneg_right (hcrit i)
    (Finset.prod_nonneg (fun j _ => hnn j))
end QEC.Coding.ProbabilisticConstruction.Resampling
