-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:33:06.385291+00:00
-- url     : https://prove2.me/submissions/dd404057-4aa4-4a09-aa68-77cf9303406e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
variable [Fintype I] [LinearOrder I] [MeasurableSpace I]
variable (B : A → I → Set W) [∀ a i, DecidablePred (· ∈ B a i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (L : List I) (a : A) (w : W) :
    firstBadFrom (B a) L w =
      firstBadFrom (fun i => {z : A × W | z.2 ∈ B z.1 i}) L (a,w) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      by_cases h : w ∈ B a i
      · simp only [firstBadFrom, h, Set.mem_setOf_eq, if_true]
      · simp only [firstBadFrom, h, Set.mem_setOf_eq, if_false, ih]
end QEC.Coding.ProbabilisticConstruction.Resampling
