-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.puncturedLogicalBasis_pairing_puncture_one_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:10:52.102671+00:00
-- url     : https://prove2.me/submissions/2bcae14c-55a9-4d17-8058-2db0d1015dfc

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_puncturedLogicalWord_pairing_puncture_one_eq_neg_sum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
    (data : SourceInput F I Logical) (a : Logical) :
    wordPairing (data.puncturedLogicalWord (canonicalBasisWord a))
      (data.puncture (1 : Word F I)) = -1 := by
  simpa [canonicalBasisWord] using
    data.puncturedLogicalWord_pairing_puncture_one_eq_neg_sum (canonicalBasisWord a)
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
