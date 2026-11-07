-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.wordPairing_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:45:58.911291+00:00
-- url     : https://prove2.me/submissions/909988bd-93e5-419f-a633-be1762f3378c

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
    (left right : Word F I) :
    wordPairing left right =
      wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) +
        wordPairing (data.puncture left) (data.puncture right) := by
  classical
  letI : Fintype (Set.range data.pivotEmbedding) :=
    Fintype.subtype (Finset.univ.filter fun i => i ∈ Set.range data.pivotEmbedding)
      (by simp)
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : I => i ∈ Set.range data.pivotEmbedding)
    (fun i => left i * right i)
  let rangeEquiv : Logical ≃ Set.range data.pivotEmbedding :=
    Equiv.ofInjective data.pivotEmbedding data.pivotEmbedding.injective
  have hrange :
      (∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1) =
        ∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a) := by
    exact Fintype.sum_equiv rangeEquiv.symm
      (fun point => left point.1 * right point.1)
      (fun a => left (data.pivotEmbedding a) * right (data.pivotEmbedding a))
      (fun point => by
        have hpoint : data.pivotEmbedding (rangeEquiv.symm point) = point.1 :=
          congrArg Subtype.val (rangeEquiv.apply_symm_apply point)
        change left point.1 * right point.1 =
          left (data.pivotEmbedding (rangeEquiv.symm point)) *
            right (data.pivotEmbedding (rangeEquiv.symm point))
        rw [hpoint])
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
    wordPairing left right = ∑ point : I, left point * right point := rfl
    _ = (∑ point : Set.range data.pivotEmbedding, left point.1 * right point.1) +
        ∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
          left point.1 * right point.1 := hsplit.symm
    _ = (∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a)) +
        ∑ point : {i : I // ¬ i ∈ Set.range data.pivotEmbedding},
          left point.1 * right point.1 := by rw [hrange]
    _ = (∑ a : Logical, left (data.pivotEmbedding a) * right (data.pivotEmbedding a)) +
        ∑ point : data.PivotComplement, left point.1 * right point.1 := by rw [hcomplement]
    _ = wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) +
        wordPairing (data.puncture left) (data.puncture right) := rfl
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
