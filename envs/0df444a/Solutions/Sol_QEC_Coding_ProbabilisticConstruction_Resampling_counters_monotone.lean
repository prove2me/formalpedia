-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.counters_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:27.804015+00:00
-- url     : https://prove2.me/submissions/e87e25b2-d92b-4445-9c13-870df43a61c5

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_le_advance
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_succ_of_none
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_succ_of_some

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (v : V) :
    Monotone (fun n => counters vars bad R n v) := by
  apply monotone_nat_of_le_succ
  intro n
  cases h : selected vars bad R n with
  | none => rw [counters_succ_of_none vars bad R n h]
  | some i => rw [counters_succ_of_some vars bad R n i h]; exact le_advance _ _ _ _
end QEC.Coding.ProbabilisticConstruction.Resampling
