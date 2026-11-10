-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.expected_prefixCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:38:19.243862+00:00
-- url     : https://prove2.me/submissions/306ebc2c-3dea-4d97-9055-a3825a8df634

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_eventProbability_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_compatible
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_le_compatible
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_tree_compatibility_probability_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_le_budget
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_nonneg
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
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (T : ℕ) (i : I) :
    (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞) ∂tableLaw ν) ≤
      ENNReal.ofReal (resamplingBudget x i) := by
  classical
  let S : WitnessTree (supportGraph vars) (T + 1) i → Set (Table (X := X)) :=
    fun t => compatible vars bad i (witnessPaths (supportGraph vars) (T + 1) i t)
  have hS : ∀ t, MeasurableSet (S t) := fun t => measurableSet_compatible vars bad hbad i _
  calc
    (∫⁻ R, (prefixCount vars bad R T i : ℝ≥0∞) ∂tableLaw ν) ≤
        ∫⁻ R, ∑ t, (S t).indicator (fun _ => (1 : ℝ≥0∞)) R ∂tableLaw ν := by
      apply lintegral_mono
      intro R
      have hc := prefixCount_le_compatible vars bad R T i
      have hcast := (Nat.cast_le (α := ℝ≥0∞)).mpr hc
      simpa only [Finset.natCast_card_filter, Set.indicator_apply] using hcast
    _ = ∑ t, tableLaw ν (S t) := by
      rw [lintegral_finsetSum _ (fun t _ => measurable_const.indicator (hS t))]
      apply Finset.sum_congr rfl
      intro t ht
      change (∫⁻ R, (S t).indicator 1 R ∂tableLaw ν) = _
      exact lintegral_indicator_one (μ := tableLaw ν) (hS t)
    _ ≤ ∑ t : WitnessTree (supportGraph vars) (T + 1) i,
        ENNReal.ofReal (witnessWeight (supportGraph vars) (eventProbability vars ν bad) (T + 1) i t) := by
      apply Finset.sum_le_sum
      intro t ht
      exact tree_compatibility_probability_le vars ν bad hbad (T + 1) i t
    _ = ENNReal.ofReal (witnessPartition (supportGraph vars)
        (eventProbability vars ν bad) (T + 1) i) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg
        (fun t _ => witnessWeight_nonneg _ _ (eventProbability_nonneg vars ν bad) _ _ t)
    _ ≤ ENNReal.ofReal (resamplingBudget x i) := ENNReal.ofReal_le_ofReal
      (witnessPartition_le_budget _ _ x (eventProbability_nonneg vars ν bad)
        hx0 hx1 hcrit (T + 1) i)
end QEC.Coding.ProbabilisticConstruction.Resampling
