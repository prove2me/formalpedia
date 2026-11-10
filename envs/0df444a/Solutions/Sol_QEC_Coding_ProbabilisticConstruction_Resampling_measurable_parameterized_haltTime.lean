-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_haltTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:40:04.813769+00:00
-- url     : https://prove2.me/submissions/9d62eec7-9d71-4286-86e9-40fd7eabd08a

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_selected
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_parameterized_halts
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
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
    Measurable (fun z : A × Table (X := X) => haltTime vars (bad z.1) z.2) := by
  classical
  let p : (A × Table (X := X)) → ℕ → Prop := fun z n =>
    selected vars (bad z.1) z.2 n = none ∨ ¬ Halts vars (bad z.1) z.2
  have hp : ∀ z, ∃ n, p z n := by
    intro z
    by_cases hz : Halts vars (bad z.1) z.2
    · obtain ⟨n,hn⟩ := hz
      exact ⟨n,Or.inl hn⟩
    · exact ⟨0,Or.inr hz⟩
  have hm : Measurable (fun z => Nat.find (hp z)) :=
    measurable_find hp fun n =>
      ((measurable_parameterized_selected vars bad hbad n) (measurableSet_singleton none)).union
        (measurableSet_parameterized_halts vars bad hbad).compl
  convert hm using 1
  funext z
  by_cases hz : Halts vars (bad z.1) z.2
  · simp only [haltTime, dif_pos hz]
    symm
    exact Nat.find_congr' (by intro n; simp [p,hz])
  · simp only [haltTime, dif_neg hz]
    symm
    exact Nat.find_eq_zero (hp z) |>.mpr (Or.inr hz)
end QEC.Coding.ProbabilisticConstruction.Resampling
