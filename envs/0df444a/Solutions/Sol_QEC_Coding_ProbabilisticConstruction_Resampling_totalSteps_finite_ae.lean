-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.totalSteps_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:43:08.35703+00:00
-- url     : https://prove2.me/submissions/533cb348-d27a-43e2-9517-369d3b6bea40

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalSteps
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_totalSteps_le

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
theorem _root_.solution : ∀ᵐ R ∂tableLaw ν, totalSteps vars bad R < ∞ := by
  apply ae_lt_top (measurable_totalSteps vars bad hbad)
  exact (lt_of_le_of_lt (expected_totalSteps_le vars bad ν hbad x hx0 hx1 hcrit)
    ENNReal.ofReal_lt_top).ne
end QEC.Coding.ProbabilisticConstruction.Resampling
