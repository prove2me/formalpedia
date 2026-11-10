-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:38:04.805202+00:00
-- url     : https://prove2.me/submissions/410c5f6f-812f-49b0-a880-a2a8227045d3

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_select
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_parameterized_localEvent
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_counters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {A V I : Type*} [MeasurableSpace A]
variable [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : A → ∀ i, Set (∀ v : vars i, X v))
variable [∀ a i, DecidablePred (· ∈ bad a i)]
variable (hbad : ∀ i, MeasurableSet
  {z : A × (∀ v : vars i, X v) | z.2 ∈ bad z.1 i})
include hbad
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (n : ℕ) :
    Measurable (fun z : A × Table (X := X) => selected vars (bad z.1) z.2 n) :=
  (measurable_parameterized_select (fun a => localEvent vars (bad a))
    (measurableSet_parameterized_localEvent vars bad hbad)).comp
      (measurable_fst.prodMk (measurable_parameterized_assignment
        (measurable_parameterized_counters vars bad hbad n)))
end QEC.Coding.ProbabilisticConstruction.Resampling
