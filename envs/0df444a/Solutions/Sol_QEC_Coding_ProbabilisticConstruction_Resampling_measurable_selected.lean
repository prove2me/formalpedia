-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:38.445574+00:00
-- url     : https://prove2.me/submissions/c3461e66-0b7f-473a-9724-55536a537a16

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_select
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_counters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_localEvent


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (hbad : ∀ i, MeasurableSet (bad i)) (n : ℕ) :
    Measurable (fun R : Table (X := X) => selected vars bad R n) :=
  (measurable_select _ (measurableSet_localEvent vars bad hbad)).comp
    (measurable_assignment (measurable_counters vars bad hbad n))
end QEC.Coding.ProbabilisticConstruction.Resampling
