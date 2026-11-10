-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_haltTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:30:28.11348+00:00
-- url     : https://prove2.me/submissions/f717c5f9-b442-4ffc-92a4-e7957c2c8f23

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_halts
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_selected
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
include hbad
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution : Measurable (haltTime vars bad (X := X)) := by
  classical
  let p : Table (X := X) → ℕ → Prop := fun R n =>
    selected vars bad R n = none ∨ ¬ Halts vars bad R
  have hp : ∀ R, ∃ n, p R n := by
    intro R
    by_cases hR : Halts vars bad R
    · obtain ⟨n, hn⟩ := hR; exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hR⟩
  have hm : Measurable (fun R => Nat.find (hp R)) := measurable_find hp (fun n =>
    ((measurable_selected vars bad hbad n) (measurableSet_singleton none)).union
      (measurableSet_halts vars bad hbad).compl)
  convert hm using 1
  funext R
  by_cases hR : Halts vars bad R
  · simp only [haltTime, dif_pos hR]
    symm
    exact Nat.find_congr' (by intro n; simp [p, hR])
  · simp only [haltTime, dif_neg hR]
    symm
    exact Nat.find_eq_zero (hp R) |>.mpr (Or.inr hR)
end QEC.Coding.ProbabilisticConstruction.Resampling
