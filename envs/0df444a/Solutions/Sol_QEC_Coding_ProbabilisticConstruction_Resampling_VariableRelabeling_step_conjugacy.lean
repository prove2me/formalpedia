-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.step_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:41:31.77921+00:00
-- url     : https://prove2.me/submissions/cc69ca14-05cf-443a-85b0-a5cc0b50345d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_assignment
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_select_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_assignment_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_advance_conjugacy
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
section
noncomputable section
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]
variable (u : A ≃ V) (U : I → Finset V) (B : ∀ i, Set (U i → X))
variable [∀ i, DecidablePred (·∈B i)]
private theorem select_decision_eq {Ω J : Type*} [Fintype J] [LinearOrder J]
    (E : J → Set Ω) (d e : ∀ i, DecidablePred (·∈E i)) (z : Ω) :
    @select Ω J E d inferInstance inferInstance z=
      @select Ω J E e inferInstance inferInstance z :=
  congrArg (fun f : ∀ i, DecidablePred (·∈E i) =>
    @select Ω J E f inferInstance inferInstance z) (Subsingleton.elim d e)
section Measurable
variable [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
end Measurable
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
end
end

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
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
theorem _root_.solution (T : HTable V X) (c : Counters V) :
    step (codedSupport u U) (codedBad u U B) (encodeTable u T) (encodeAssignment u c)=
      encodeAssignment u (step U B T c) := by
  let ea : I → Set (A → X) :=
    localEvent (X := fun _ : A => X) (codedSupport u U) (codedBad (X := X) u U B)
  let ev : I → Set (V → X) := localEvent (X := fun _ : V => X) U B
  have hsel : select (ea)
      (assignment (encodeTable u T) (encodeAssignment u c))=
      select (ev) (assignment T c) :=
    (congrArg (fun z : A → X =>
      select (ea) z)
      (assignment_conjugacy u T c)).trans
      ((select_conjugacy (X := X) u U B (encodeAssignment u (assignment T c))).trans
        (congrArg (fun z : V → X => select (ev) z)
          (decode_encode_assignment u (assignment T c))))
  let da := decidableLocalEvents (X := fun _ : A => X)
    (codedSupport u U) (codedBad (X := X) u U B)
  let dv := decidableLocalEvents (X := fun _ : V => X) U B
  let ca : (i : I) → (z : A → X) → Decidable (z∈ea i) :=
    fun (i : I) (z : A → X) => Classical.propDecidable (z∈ea i)
  let cv : (i : I) → (z : V → X) → Decidable (z∈ev i) :=
    fun (i : I) (z : V → X) => Classical.propDecidable (z∈ev i)
  have hactual : @select (A → X) I
      (ea) da inferInstance inferInstance
      (assignment (encodeTable u T) (encodeAssignment u c))=
      @select (V → X) I (ev) dv inferInstance inferInstance (assignment T c) :=
    (select_decision_eq _ da ca _).trans (hsel.trans (select_decision_eq _ cv dv _))
  change (match @select (A → X) I
      (ea) da inferInstance inferInstance
      (assignment (encodeTable u T) (encodeAssignment u c)) with
      | none => encodeAssignment u c
      | some i => advance (codedSupport u U) i (encodeAssignment u c))=
    encodeAssignment u (match @select (V → X) I (ev) dv
      inferInstance inferInstance (assignment T c) with
      | none => c | some i => advance U i c)
  rw [hactual]
  cases h : @select (V → X) I (ev) dv
      inferInstance inferInstance (assignment T c) with
  | none => rfl
  | some i => exact advance_conjugacy u U i c
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
