-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:41:43.991196+00:00
-- url     : https://prove2.me/submissions/eea7ddd6-e2e1-4cb9-a904-52654f45cf89

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalCount
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_totalCount_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_resamplingBudget_nonneg


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
theorem _root_.solution :
    (∫⁻ R, totalSteps vars bad R ∂tableLaw ν) ≤
      ENNReal.ofReal (∑ i, resamplingBudget x i) := by
  unfold totalSteps
  rw [lintegral_finsetSum _ (fun i _ => measurable_totalCount vars bad hbad i)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => resamplingBudget_nonneg x hx0 hx1 i)]
  exact Finset.sum_le_sum (fun i _ => expected_totalCount_le vars bad ν hbad x hx0 hx1 hcrit i)
end QEC.Coding.ProbabilisticConstruction.Resampling
