-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_assignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:32:57.105209+00:00
-- url     : https://prove2.me/submissions/7e982595-25ad-44d0-9d44-856d974e53eb

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
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution
    {c : A × Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun z : A × Table (X := X) => assignment z.2 (c z)) := by
  apply measurable_pi_lambda
  intro v
  have lookup : Measurable (fun z : Table (X := X) × ℕ => tableRead z.1 v z.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply (v,n))
  exact lookup.comp (measurable_snd.prodMk ((measurable_pi_apply v).comp hc))
end QEC.Coding.ProbabilisticConstruction.Resampling
