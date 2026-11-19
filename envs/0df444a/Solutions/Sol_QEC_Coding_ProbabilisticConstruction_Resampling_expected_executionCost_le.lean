-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.expected_executionCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:26:39.703767+00:00
-- url     : https://prove2.me/submissions/bde044d9-3975-4136-ac5d-fbe10b294bce

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_executionCost_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_totalSteps_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halts_and_output_good_ae
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalSteps
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
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (queryCost : I → ℝ≥0∞) (sampleCost : V → ℝ≥0∞)
    (initialCost outputCost C : ℝ≥0∞) (hinit : ∑ v, sampleCost v ≤ initialCost)
    (hquery : ∀ i, queryCost i ≤ C)
    (hsample : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q) :
    (∫⁻ R, executionCost vars bad queryCost sampleCost outputCost R ∂tableLaw ν) ≤
      initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) *
          ENNReal.ofReal (∑ i, resamplingBudget x i) := by
  calc
    _ ≤ ∫⁻ R, initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) * totalSteps vars bad R ∂tableLaw ν := by
      apply lintegral_mono_ae
      filter_upwards [halts_and_output_good_ae vars bad ν hbad x hx0 hx1 hcrit] with R hR
      exact executionCost_le vars bad queryCost sampleCost initialCost outputCost C
        hinit hquery hsample q hq R hR.1
    _ = initialCost + outputCost + (Fintype.card I : ℝ≥0∞) * C +
        ((Fintype.card I : ℝ≥0∞) * C + (q : ℝ≥0∞) * C) *
          (∫⁻ R, totalSteps vars bad R ∂tableLaw ν) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _
        (measurable_totalSteps vars bad hbad)]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (expected_totalSteps_le vars bad ν hbad x hx0 hx1 hcrit))
end QEC.Coding.ProbabilisticConstruction.Resampling
