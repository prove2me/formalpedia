-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.compatibility_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:27:58.600693+00:00
-- url     : https://prove2.me/submissions/b08286de-df82-48af-b3a2-a086fb56a380

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witness_address_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_local_probability_eq
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_table_tests_probability
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
    (root : I) (P : Finset (List I)) :
    tableLaw ν (compatible vars bad root P) ≤
      ∏ p : P, (Measure.pi ν) (localEvent vars bad (pathLabel root p.val)) := by
  classical
  by_cases hd : DistinctVariableDepth vars root P
  · have he : compatible vars bad root P =
        {R | ∀ p : P, familyRead (fun q : P => vars (pathLabel root q.val))
          (fun q v => variableRank vars root P q.val v.val) R p ∈ bad (pathLabel root p.val)} := by
      ext R; simp [compatible, hd]
    rw [he, table_tests_probability ν _ _ (witness_address_injective vars root P hd)
      _ (fun p => hbad _)]
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro p hp
    exact (local_probability_eq ν _ _ (hbad _)).symm
  · have he : compatible vars bad root P = ∅ := by ext R; simp [compatible, hd]
    simp [he]
end QEC.Coding.ProbabilisticConstruction.Resampling
