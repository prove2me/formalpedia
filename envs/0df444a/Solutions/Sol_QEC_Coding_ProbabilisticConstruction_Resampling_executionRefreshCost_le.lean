-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.executionRefreshCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:23:57.28353+00:00
-- url     : https://prove2.me/submissions/b9f1b9ae-e343-49ce-980e-871afec4a846

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
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
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (sampleCost : V → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q)
    (R : Table (X := X)) (n : ℕ) :
    executionRefreshCost vars bad sampleCost R n ≤ (q : ℝ≥0∞) * C := by
  unfold executionRefreshCost
  split
  · exact zero_le
  · rename_i i hi
    calc
      ∑ v ∈ vars i, sampleCost v ≤ ∑ _v ∈ vars i, C := Finset.sum_le_sum (fun v _ => hC v)
      _ = ((vars i).card : ℝ≥0∞) * C := by simp [nsmul_eq_mul]
      _ ≤ (q : ℝ≥0∞) * C := mul_le_mul' ((Nat.cast_le (α := ℝ≥0∞)).mpr (hq i)) le_rfl
end QEC.Coding.ProbabilisticConstruction.Resampling
