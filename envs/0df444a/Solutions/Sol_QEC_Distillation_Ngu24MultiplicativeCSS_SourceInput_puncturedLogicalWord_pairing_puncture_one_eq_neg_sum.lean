-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalWord_pairing_puncture_one_eq_neg_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:49:07.316135+00:00
-- url     : https://prove2.me/submissions/de20c1d5-5242-4562-86be-9e59cac05375

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_systematicLogicalWord_mem_code
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_shortenedCode_pairing
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_wordPairing_partition
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
theorem _root_.solution
    (data : SourceInput F I Logical) (u : Word F Logical) :
    wordPairing (data.puncturedLogicalWord u) (data.puncture (1 : Word F I)) =
      -(∑ a : Logical, u a) := by
  have hfull : wordPairing (data.systematicLogicalWord u) (1 : Word F I) = 0 :=
    data.shortenedCode_pairing (data.systematicLogicalWord_mem_code u) data.one_mem_code
  have hpartition := data.wordPairing_partition (data.systematicLogicalWord u) (1 : Word F I)
  have hpivot_one : data.pivotCoordinates (1 : Word F I) = (1 : Word F Logical) := rfl
  rw [data.pivotCoordinates_systematicLogicalWord, hpivot_one, hfull] at hpartition
  have hneg : wordPairing (data.puncture (data.systematicLogicalWord u))
      (data.puncture (1 : Word F I)) = -wordPairing u (1 : Word F Logical) :=
    eq_neg_of_add_eq_zero_right hpartition.symm
  simpa [puncturedLogicalWord, wordPairing_apply, dotProduct] using hneg
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
