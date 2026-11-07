-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_counters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:18.226139+00:00
-- url     : https://prove2.me/submissions/4461bb37-0a8c-4c93-9145-f9b975e93bee

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_select
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_assignment
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
    Measurable (fun R : Table (X := X) => counters vars bad R n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs : Measurable (fun R : Table (X := X) =>
        select (localEvent vars bad) (assignment R (counters vars bad R n))) :=
      (measurable_select _ (measurableSet_localEvent vars bad hbad)).comp
        (measurable_assignment ih)
    have hu : Measurable (fun p : Counters V × Option I =>
        match p.2 with | none => p.1 | some i => advance vars i p.1) :=
      measurable_of_countable _
    exact hu.comp (ih.prodMk hs)
end QEC.Coding.ProbabilisticConstruction.Resampling
