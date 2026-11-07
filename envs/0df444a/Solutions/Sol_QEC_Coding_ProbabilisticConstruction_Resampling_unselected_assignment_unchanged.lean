-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.unselected_assignment_unchanged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:26.902712+00:00
-- url     : https://prove2.me/submissions/6a91de6d-3433-4ed0-9c93-15d6802860e7

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_succ_of_some
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) {v : V} (hv : v ∉ vars i) :
    assignment R (counters vars bad R (n + 1)) v =
      assignment R (counters vars bad R n) v := by
  rw [counters_succ_of_some vars bad R n i h]
  change tableRead R v (advance vars i (counters vars bad R n) v) =
    tableRead R v (counters vars bad R n v)
  rw [advance_of_notMem vars i _ hv]
end QEC.Coding.ProbabilisticConstruction.Resampling
