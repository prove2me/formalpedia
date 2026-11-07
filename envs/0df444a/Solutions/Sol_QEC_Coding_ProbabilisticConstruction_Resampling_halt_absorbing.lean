-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.halt_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:31.890397+00:00
-- url     : https://prove2.me/submissions/56ec3915-fdaa-45f4-b56d-767114d858d1

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_succ_of_none
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) (k : ℕ) :
    counters vars bad R (n + k) = counters vars bad R n ∧
      selected vars bad R (n + k) = none := by
  induction k with
  | zero => exact ⟨rfl, h⟩
  | succ k ih =>
    have hc : counters vars bad R (n + (k + 1)) = counters vars bad R n := by
      rw [← Nat.add_assoc, counters_succ_of_none vars bad R (n + k) ih.2, ih.1]
    exact ⟨hc, by simpa [selected, hc] using h⟩
end QEC.Coding.ProbabilisticConstruction.Resampling
