-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.shortenedCosetKet_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:22:34.230082+00:00
-- url     : https://prove2.me/submissions/2587afdf-7928-466f-a5c8-6dde3b974ede

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
theorem _root_.solution (data : SourceInput F I Logical) (u : Word F Logical)
    (h : H0 data) :
    inner Complex (registerBasisKet (data.shortenedCosetLabel u h)) (data.shortenedCosetKet u) =
      cosetNormalization (H0 data) := by
  classical
  unfold shortenedCosetKet
  rw [inner_smul_right, inner_sum]
  rw [Finset.sum_eq_single h]
  · simp [registerBasisKet]
  · intro h' _hh' hne
    have hlabel : data.shortenedCosetLabel u h' ≠ data.shortenedCosetLabel u h :=
      fun heq => hne (data.shortenedCosetLabel_injective u heq)
    simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp [hlabel.symm]
  · simp
end QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
