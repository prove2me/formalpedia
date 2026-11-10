-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:41:28.856715+00:00
-- url     : https://prove2.me/submissions/46403168-09a4-44c8-8fb4-306a98f284d2

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_counters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_haltTime

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
theorem _root_.solution :
    Measurable (fun z : A × Table (X := X) => output vars (bad z.1) z.2) := by
  have hm : Measurable (fun z : (A × Table (X := X)) × ℕ =>
      counters vars (bad z.1.1) z.1.2 z.2) :=
    measurable_from_prod_countable_left fun n => measurable_parameterized_counters vars bad hbad n
  exact measurable_parameterized_assignment
    (hm.comp (measurable_id.prodMk (measurable_parameterized_haltTime vars bad hbad)))
end QEC.Coding.ProbabilisticConstruction.Resampling
