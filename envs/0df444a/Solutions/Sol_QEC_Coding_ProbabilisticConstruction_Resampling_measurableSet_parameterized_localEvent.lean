-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurableSet_parameterized_localEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:33:03.859388+00:00
-- url     : https://prove2.me/submissions/1a51d965-ee20-4842-8a1f-689779fc19be

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution

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
theorem _root_.solution (i : I) :
    MeasurableSet {z : A × (∀ v, X v) | z.2 ∈ localEvent vars (bad z.1) i} := by
  have hm : Measurable (fun z : A × (∀ v, X v) =>
      (z.1, fun v : vars i => z.2 v.val)) :=
    measurable_fst.prodMk (measurable_pi_lambda _ fun v : vars i =>
      (measurable_pi_apply v.val).comp measurable_snd)
  exact (hbad i).preimage hm
end QEC.Coding.ProbabilisticConstruction.Resampling
