-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:50:21.395405+00:00
-- url     : https://prove2.me/submissions/d2f70f80-8161-4e1d-9583-b5a5ce9658b3

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_counters_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_selected_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_halts_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_haltTime_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_output_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_prefixCount_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_totalCount_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_totalSteps_conjugacy
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


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_assignment
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_assignment
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_table
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.encode_decode_table

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]
variable (u : A ≃ V) (U : I → Finset V) (B : ∀ i, Set (U i → X))
variable [∀ i, DecidablePred (·∈B i)]
variable [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
theorem _root_.solution (T : HTable V X) :
    decodedObservation u U B (encodeTable u T)=jointObservation U B T := by
  have hc : (fun m => decodeAssignment u
      (counters (codedSupport u U) (codedBad u U B) (encodeTable u T) m))=
      counters U B T := by
    funext m
    exact (congrArg (decodeAssignment u) (counters_conjugacy u U B T m)).trans
      (decode_encode_assignment u (counters U B T m))
  have hs : selected (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      selected U B T := funext (selected_conjugacy u U B T)
  have hh : (if Halts (codedSupport u U) (codedBad u U B) (encodeTable u T)
      then true else false)=(if Halts U B T then true else false) := by
    by_cases h : Halts U B T
    · have hcode := (halts_conjugacy u U B T).mpr h
      exact (if_pos hcode).trans (if_pos h).symm
    · have hcode : ¬Halts (codedSupport u U) (codedBad u U B) (encodeTable u T) :=
        fun hcode => h ((halts_conjugacy u U B T).mp hcode)
      exact (if_neg hcode).trans (if_neg h).symm
  have ho : decodeAssignment u
      (output (codedSupport u U) (codedBad u U B) (encodeTable u T))=output U B T :=
    (congrArg (decodeAssignment u) (output_conjugacy u U B T)).trans
      (decode_encode_assignment u (output U B T))
  have hp : prefixCount (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      prefixCount U B T := by
    funext m i
    exact prefixCount_conjugacy u U B T m i
  have ht : totalCount (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      totalCount U B T := funext (totalCount_conjugacy u U B T)
  exact Prod.ext hc (Prod.ext hs (Prod.ext hh (Prod.ext (haltTime_conjugacy u U B T)
    (Prod.ext ho (Prod.ext hp (Prod.ext ht (totalSteps_conjugacy u U B T)))))))
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
