-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.scanCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:29:58.252199+00:00
-- url     : https://prove2.me/submissions/f089d54e-8929-45cf-a95f-95e67dc4e797

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
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (queryCost : I → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ i, queryCost i ≤ C) (L : List I) (ω : Ω) :
    scanCost B queryCost L ω ≤ (L.length : ℝ≥0∞) * C := by
  induction L with
  | nil => simp [scanCost]
  | cons i L ih =>
    simp only [scanCost, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      queryCost i + (if ω ∈ B i then 0 else scanCost B queryCost L ω) ≤
          C + (L.length : ℝ≥0∞) * C := add_le_add (hC i) (by split_ifs <;> simp_all)
      _ = ((L.length : ℝ≥0∞) + 1) * C := by ring
end QEC.Coding.ProbabilisticConstruction.Resampling
