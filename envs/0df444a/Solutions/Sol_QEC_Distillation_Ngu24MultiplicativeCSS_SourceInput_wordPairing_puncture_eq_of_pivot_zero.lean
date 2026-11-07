-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.wordPairing_puncture_eq_of_pivot_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:33.150207+00:00
-- url     : https://prove2.me/submissions/8eae8e54-b371-4f1d-a7fc-a9e8ca35b5f6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_25
open QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
namespace QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
theorem _root_.solution (data : SourceInput F I Logical)
    (left right : Word F I) (hzero : data.pivotCoordinates left = 0) :
    wordPairing (data.puncture left) (data.puncture right) = wordPairing left right := by
  classical
  letI : Fintype (Set.range data.pivotEmbedding) :=
    Fintype.subtype (Finset.univ.filter fun i => i ∈ Set.range data.pivotEmbedding)
      (by simp)
  have hpivot (point : {i : I // i ∈ Set.range data.pivotEmbedding}) :
      left point.1 = 0 := by
    rcases point.2 with ⟨a, ha⟩
    rw [← ha]
    exact congrFun hzero a
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => i ∈ Set.range data.pivotEmbedding)
    (fun i => left i * right i)
  have hpivot_sum :
      (∑ point : {i : I // i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    rw [hpivot point]
    simp
  have hsplit' :
      (∑ point : {i : I // i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) +
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : I, left point * right point := by
    exact hsplit
  let complementEquiv : {i : I // ¬ i ∈ Set.range data.pivotEmbedding} ≃
      data.PivotComplement := Equiv.refl _
  have hcomplement :
      (∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementEquiv
      (fun point => left point.1 * right point.1)
      (fun point => left point.1 * right point.1) (fun _ => rfl)
  calc
    wordPairing (data.puncture left) (data.puncture right) =
        ∑ point : data.PivotComplement, left point.1 * right point.1 := rfl
    _ = ∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
        left point.1 * right point.1 := hcomplement.symm
    _ = ∑ point : I, left point * right point := by
      rw [hpivot_sum, zero_add] at hsplit'
      exact hsplit'
    _ = wordPairing left right := rfl
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
