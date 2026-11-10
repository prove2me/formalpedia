-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:31:42.949132+00:00
-- url     : https://prove2.me/submissions/fe9d6d5b-34ad-4b1f-8a0f-f3116be29fb8

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_haltTime
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_counters


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
theorem _root_.solution : Measurable (output vars bad (X := X)) := by
  have hm : Measurable (fun z : Table (X := X) × ℕ => counters vars bad z.1 z.2) :=
    measurable_from_prod_countable_left (fun n => measurable_counters vars bad hbad n)
  exact measurable_assignment (hm.comp (measurable_id.prodMk (measurable_haltTime vars bad hbad)))
end QEC.Coding.ProbabilisticConstruction.Resampling
