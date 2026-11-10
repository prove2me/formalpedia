-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionRefreshCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:30:44.12487+00:00
-- url     : https://prove2.me/submissions/490d7b9f-a3e4-42c0-8af7-9d8c6de792a4

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_selected


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
include hbad
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (sampleCost : V → ℝ≥0∞) (n : ℕ) :
    Measurable (fun R : Table (X := X) => executionRefreshCost vars bad sampleCost R n) := by
  have hm : Measurable (fun j : Option I => match j with
      | none => (0 : ℝ≥0∞) | some i => ∑ v ∈ vars i, sampleCost v) :=
    measurable_of_countable _
  exact hm.comp (measurable_selected vars bad hbad n)
end QEC.Coding.ProbabilisticConstruction.Resampling
