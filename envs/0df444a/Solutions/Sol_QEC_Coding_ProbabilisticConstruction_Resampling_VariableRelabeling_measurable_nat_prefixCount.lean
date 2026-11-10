-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_nat_prefixCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:37:29.459378+00:00
-- url     : https://prove2.me/submissions/1dd0a5ac-9779-481a-b6fe-9299908732e5

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_encode_decode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_selected
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_succ
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
theorem _root_.solution (hB : ∀ i, MeasurableSet (B i)) (m : ℕ) (i : I) :
    Measurable (fun T : HTable V X => prefixCount U B T m i) := by
  induction m with
  | zero => simpa only [prefixCount,occurrences,Finset.range_zero,Finset.filter_empty,Finset.card_empty]
      using (measurable_const : Measurable (fun _ : HTable V X => (0 : ℕ)))
  | succ m ih =>
      have hsel : Measurable (fun T : HTable V X => selected U B T m) :=
        measurable_selected (X := fun _ : V => X) U B hB m
      have he : MeasurableSet {T : HTable V X | selected U B T m=some i} :=
        hsel (measurableSet_singleton (some i))
      have hm : Measurable (fun T : HTable V X => if selected U B T m=some i then (1 : ℕ) else 0) :=
        Measurable.ite he measurable_const measurable_const
      have hsum := ih.add hm
      have hpoint : ((fun T : HTable V X => prefixCount U B T m i)+
          (fun T : HTable V X => if selected U B T m=some i then (1 : ℕ) else 0))=
          (fun T : HTable V X => prefixCount U B T m i+
            if selected U B T m=some i then (1 : ℕ) else 0) :=
        funext (fun T => Pi.add_apply _ _ T)
      rw [hpoint] at hsum
      simpa only [prefixCount_succ] using hsum
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
