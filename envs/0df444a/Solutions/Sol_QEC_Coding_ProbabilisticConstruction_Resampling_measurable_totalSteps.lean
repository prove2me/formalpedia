-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_totalSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:34:55.008724+00:00
-- url     : https://prove2.me/submissions/eb17b8af-0431-4490-9223-371429a78e55

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalCount

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
include hbad
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution : Measurable (totalSteps vars bad (X := X)) :=
  Finset.measurable_sum _ (fun i _ => measurable_totalCount vars bad hbad i)
end QEC.Coding.ProbabilisticConstruction.Resampling
