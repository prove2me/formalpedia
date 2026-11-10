-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_counters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:36:55.929773+00:00
-- url     : https://prove2.me/submissions/52c1315f-441a-4b43-88f6-40b2b2a65a4c

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_step

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
    Measurable (fun z : A × Table (X := X) => counters vars (bad z.1) z.2 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_parameterized_step vars bad hbad ih
end QEC.Coding.ProbabilisticConstruction.Resampling
