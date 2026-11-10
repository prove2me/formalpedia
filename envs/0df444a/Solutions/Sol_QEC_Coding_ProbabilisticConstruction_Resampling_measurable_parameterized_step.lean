-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:35:54.38364+00:00
-- url     : https://prove2.me/submissions/f2eb10c8-1581-4a94-ad72-5d17bc873164

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_select
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_parameterized_localEvent
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_assignment

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
theorem _root_.solution
    {c : A × Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun z : A × Table (X := X) => step vars (bad z.1) z.2 (c z)) := by
  have hselect : Measurable (fun z : A × Table (X := X) =>
      select (localEvent vars (bad z.1)) (assignment z.2 (c z))) :=
    (measurable_parameterized_select (fun a => localEvent vars (bad a))
      (measurableSet_parameterized_localEvent vars bad hbad)).comp
        (measurable_fst.prodMk (measurable_parameterized_assignment hc))
  have update : Measurable (fun z : Counters V × Option I =>
      match z.2 with | none => z.1 | some i => advance vars i z.1) := by
    apply measurable_from_prod_countable_left
    intro choice
    cases choice with
    | none => exact measurable_id
    | some i =>
        apply measurable_pi_lambda
        intro v
        exact (measurable_pi_apply v).add_const _
  exact update.comp (hc.prodMk hselect)
end QEC.Coding.ProbabilisticConstruction.Resampling
