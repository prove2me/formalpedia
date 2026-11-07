-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:24.884239+00:00
-- url     : https://prove2.me/submissions/7895b40a-096d-4d43-ad14-41782a199341

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
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
theorem _root_.solution (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h : ℕ) (i : I) (t : WitnessTree G h i) : 0 ≤ witnessWeight G p h i t := by
  induction h generalizing i with
  | zero => exact PEmpty.elim t
  | succ h ih =>
    apply mul_nonneg (hp i)
    apply Finset.prod_nonneg
    intro j hj
    cases hc : t j with
    | none => simp [hc]
    | some child => exact ih j child
end QEC.Coding.ProbabilisticConstruction.Resampling
