-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_dichotomy_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:56:42.358894+00:00
-- url     : https://prove2.me/submissions/825038ac-4c3d-482c-9502-7d361d7b965e

import Definitions.Def_QEC_Import_Compact_7570c1793ee5f33c
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_externalBoundary_sector_dichotomy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_externalBoundarySector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_dichotomy_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_sector_dichotomy_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «hC» «component»
  let H := M.firstCutGlobalCoordinateTransport region
  let Zx : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.firstCutProjectorMC region) component))
  have hHcode : H.conjOperator M.fullCodeProjector = M.firstCutCodeLift region := by
    simpa [H] using M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHsector : H.conjOperator Zx = M.firstCutSectorLift region component := by
    simpa [H, Zx] using
      M.firstCutGlobalCoordinateTransport_conj_externalBoundarySector region component
  rcases M.firstCut_externalBoundary_sector_dichotomy region hC component with hzero | hfull
  · left
    calc
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          H.conjOperator M.fullCodeProjector * H.conjOperator Zx := by
        rw [hHcode, hHsector]
      _ = H.conjOperator (M.fullCodeProjector * Zx) :=
        (Semantics.UnitaryTransport.conjOperator_mul H _ _).symm
      _ = H.conjOperator 0 := congrArg H.conjOperator (by simpa [Zx] using hzero)
      _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]
  · right
    calc
      M.firstCutCodeLift region * M.firstCutSectorLift region component =
          H.conjOperator M.fullCodeProjector * H.conjOperator Zx := by
        rw [hHcode, hHsector]
      _ = H.conjOperator (M.fullCodeProjector * Zx) :=
        (Semantics.UnitaryTransport.conjOperator_mul H _ _).symm
      _ = H.conjOperator M.fullCodeProjector :=
        congrArg H.conjOperator (by simpa [Zx] using hfull)
      _ = M.firstCutCodeLift region := hHcode
end QEC.Bounds.BPTCommutingProjectorModel
