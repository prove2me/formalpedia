-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.logicalBasisTriplePairing_eq_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:18:22.289575+00:00
-- url     : https://prove2.me/submissions/62c2a2e9-577e-42fc-bfaa-ec79c91b76a8

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics
open scoped BigOperators
open Ngu24MultiplicativeCSS
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_df646da45e_25
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_df646da45e_26
omit [Fintype F] [Algebra (ZMod 2) F]
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution (a b c : Logical) :
    wordTriplePairing (canonicalBasisWord (F := F) a) (canonicalBasisWord (F := F) b)
      (canonicalBasisWord (F := F) c) = if a = b ∧ b = c then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    by_cases hbc : a = c
    · subst c
      simp [wordTriplePairing, wordStar, wordPairing_apply, canonicalBasisWord]
    · simp [wordTriplePairing, wordStar, wordPairing_apply, canonicalBasisWord, hbc]
  · by_cases hac : a = c
    · subst c
      simp [wordTriplePairing, wordStar, wordPairing_apply, canonicalBasisWord, hab]
    · by_cases hbc : b = c
      · subst c
        simp [wordTriplePairing, wordStar, wordPairing_apply, canonicalBasisWord, hab]
      · simp [wordTriplePairing, wordStar, wordPairing_apply, canonicalBasisWord,
          hab, hac, hbc]
end QEC.Distillation.Ngu24MultiplicativeCCZ
