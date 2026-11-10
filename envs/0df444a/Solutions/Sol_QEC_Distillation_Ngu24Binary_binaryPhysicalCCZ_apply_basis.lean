-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:01:29.413941+00:00
-- url     : https://prove2.me/submissions/50c44b92-968b-4549-9103-31a817ee171d

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPhysicalCCZ_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi2_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi3_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply
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
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply
attribute [local simp] QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply
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
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryPhysicalCCZ (registerBasisKet label) =
      PauliSymplectic.binaryPhaseScalar (binarySelectedExponent label) • registerBasisKet label := by
  ext target
  by_cases h : target = label
  · subst target
    simp [binaryPhysicalCCZ_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [binaryPhysicalCCZ_apply, registerBasisKet, EuclideanSpace.basisFun_apply, h]
end QEC.Distillation.Ngu24Binary
