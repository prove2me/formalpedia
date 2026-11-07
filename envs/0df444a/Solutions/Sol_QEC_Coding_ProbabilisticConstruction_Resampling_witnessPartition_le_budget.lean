-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:15.108075+00:00
-- url     : https://prove2.me/submissions/ff921131-4c84-4b2a-8441-220a896cbec2

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_succ
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_resamplingBudget_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_branching_budget_bound
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
theorem _root_.solution (p x : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, p i ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
    (h : ℕ) (i : I) : witnessPartition G p h i ≤ resamplingBudget x i := by
  induction h generalizing i with
  | zero => simpa using resamplingBudget_nonneg x hx0 hx1 i
  | succ h ih =>
    rw [witnessPartition_succ]
    apply le_trans _ (branching_budget_bound G p x hx0 hx1 hcrit i)
    apply mul_le_mul_of_nonneg_left _ (hp i)
    apply Finset.prod_le_prod
    · intro j hj; exact add_nonneg (by norm_num) (witnessPartition_nonneg G p hp h j)
    · intro j hj; exact add_le_add le_rfl (ih j)
end QEC.Coding.ProbabilisticConstruction.Resampling
