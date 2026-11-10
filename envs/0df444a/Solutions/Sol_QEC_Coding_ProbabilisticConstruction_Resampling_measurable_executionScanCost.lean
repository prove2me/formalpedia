-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_executionScanCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:31:48.7082+00:00
-- url     : https://prove2.me/submissions/271f6b6d-4a18-4b14-9eec-dd9fc1a253d0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_scanCost
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_counters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_localEvent


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
theorem _root_.solution (queryCost : I → ℝ≥0∞) (n : ℕ) :
    Measurable (fun R : Table (X := X) => executionScanCost vars bad queryCost R n) :=
  (measurable_scanCost _ (measurableSet_localEvent vars bad hbad) queryCost _).comp
    (measurable_assignment (measurable_counters vars bad hbad n))
end QEC.Coding.ProbabilisticConstruction.Resampling
