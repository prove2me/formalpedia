-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.executionCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:25:09.081358+00:00
-- url     : https://prove2.me/submissions/3ef71672-c3f3-4a3d-a57d-641f72b70d78

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_executionScanCost_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_executionRefreshCost_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_totalSteps_eq_haltTime
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
theorem _root_.solution (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (initialCost outputCost C : ℝ≥0∞) (hinit : ∑ v, sampleCost v ≤ initialCost)
    (hquery : ∀ i, queryCost i ≤ C)
    (hsample : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q)
    (R : Table (X := X)) (hR : Halts vars bad R) :
    executionCost vars bad queryCost sampleCost outputCost R ≤
      initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) * totalSteps vars bad R := by
  rw [executionCost, if_pos hR, totalSteps_eq_haltTime vars bad R hR]
  calc
    _ ≤ initialCost + outputCost +
        (∑ _n ∈ Finset.range (haltTime vars bad R + 1), (Fintype.card I : ℝ≥0∞) * C) +
        ∑ _n ∈ Finset.range (haltTime vars bad R), (q : ℝ≥0∞) * C := by
      apply add_le_add
      · exact add_le_add (add_le_add hinit le_rfl)
          (Finset.sum_le_sum (fun n _ => executionScanCost_le vars bad queryCost C hquery R n))
      · exact Finset.sum_le_sum (fun n _ => executionRefreshCost_le vars bad sampleCost C hsample q hq R n)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]; ring
end QEC.Coding.ProbabilisticConstruction.Resampling
