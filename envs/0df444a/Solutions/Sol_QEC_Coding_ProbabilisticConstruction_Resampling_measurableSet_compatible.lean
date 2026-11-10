-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurableSet_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:21:42.654202+00:00
-- url     : https://prove2.me/submissions/4546be88-fe8f-4ad8-a1b0-9d5fdfdff2b8

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_familyRead
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (hbad : ∀ i, MeasurableSet (bad i))
    (root : I) (P : Finset (List I)) : MeasurableSet (compatible vars bad root P) := by
  classical
  by_cases hd : DistinctVariableDepth vars root P
  · have hm := measurable_familyRead (X := X) (fun q : P => vars (pathLabel root q.val))
      (fun q v => variableRank vars root P q.val v.val)
    have he : compatible vars bad root P =
        familyRead (fun q : P => vars (pathLabel root q.val))
          (fun q v => variableRank vars root P q.val v.val) ⁻¹'
            Set.univ.pi (fun q : P => bad (pathLabel root q.val)) := by
      ext R; simp [compatible, hd]
    rw [he]
    exact (MeasurableSet.univ_pi (fun q => hbad _)).preimage hm
  · have he : compatible vars bad root P = ∅ := by ext R; simp [compatible, hd]
    rw [he]; exact MeasurableSet.empty
end QEC.Coding.ProbabilisticConstruction.Resampling
