-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.selected_none_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:21.278562+00:00
-- url     : https://prove2.me/submissions/2b91b152-bef3-4c9f-be08-7dd33afff30e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_none_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) :
    ∀ i, assignment R (counters vars bad R n) ∉ localEvent vars bad i :=
  (select_none_iff _ _).mp h
end QEC.Coding.ProbabilisticConstruction.Resampling
