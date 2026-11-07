-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:22.171473+00:00
-- url     : https://prove2.me/submissions/2770f4e3-bd65-4b13-98b2-89edfe0f5bb2

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
theorem _root_.solution (p : I → ℝ) (h : ℕ) (i : I) :
    witnessPartition G p (h + 1) i =
      p i * ∏ j ∈ closedNeighbors G i, (1 + witnessPartition G p h j) := by
  classical
  change (∑ t : (∀ j : closedNeighbors G i, Option (WitnessTree G h j)),
    p i * ∏ j : closedNeighbors G i, (t j).elim 1 (witnessWeight G p h j)) = _
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (j : closedNeighbors G i)
    (child : Option (WitnessTree G h j)) => child.elim 1 (witnessWeight G p h j))]
  congr 1
  simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
    witnessPartition] using
    (Finset.prod_coe_sort (closedNeighbors G i) (fun j => 1 +
      ∑ t : WitnessTree G h j, witnessWeight G p h j t))
end QEC.Coding.ProbabilisticConstruction.Resampling
