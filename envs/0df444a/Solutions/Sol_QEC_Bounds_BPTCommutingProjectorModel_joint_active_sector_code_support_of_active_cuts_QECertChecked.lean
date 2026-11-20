-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.joint_active_sector_code_support_of_active_cuts_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:56:55.055827+00:00
-- url     : https://prove2.me/submissions/bc3891bf-47db-46b2-a6fb-7ff18a99a580

import Definitions.Def_QEC_Import_Compact_42780ddc06139287
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_symm_conj_internalBoundaryLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_externalBoundarySector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_fullCodeProjector
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
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.joint_active_sector_code_support_of_active_cuts_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.joint_active_sector_code_support_of_active_cuts_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «ccomponent» «bcomponent» «hCactive» «hBactive»
  let Pi := M.fullCodeProjector
  let ZC : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
      ((M.fourFactorCCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent))
  let ZB : Semantics.Operator L.Register :=
    (M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
      ((M.fourFactorBCoordinateRelabel region).symm.conjOperator
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) bcomponent))
  let HC := M.firstCutGlobalCoordinateTransport region
  have hHCcode : HC.conjOperator Pi = M.firstCutCodeLift region := by
    simpa [HC, Pi] using M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHCsector : HC.conjOperator ZC = M.firstCutSectorLift region ccomponent := by
    simpa [HC, ZC] using
      M.firstCutGlobalCoordinateTransport_conj_externalBoundarySector region ccomponent
  have hCactiveTransport :
      HC.conjOperator Pi * HC.conjOperator ZC = HC.conjOperator Pi := by
    calc
      HC.conjOperator Pi * HC.conjOperator ZC =
          M.firstCutCodeLift region * M.firstCutSectorLift region ccomponent :=
        congrArg₂ (· * ·) hHCcode hHCsector
      _ = M.firstCutCodeLift region := hCactive
      _ = HC.conjOperator Pi := hHCcode.symm
  have hCphysical : Pi * ZC = Pi := by
    calc
      Pi * ZC = HC.symm.conjOperator (HC.conjOperator (Pi * ZC)) :=
        (HC.symm_conjOperator_conjOperator _).symm
      _ = HC.symm.conjOperator (HC.conjOperator Pi * HC.conjOperator ZC) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul]
      _ = HC.symm.conjOperator (HC.conjOperator Pi) :=
        congrArg HC.symm.conjOperator hCactiveTransport
      _ = Pi := HC.symm_conjOperator_conjOperator Pi
  let HB := M.secondCutGlobalCoordinateTransport region
  have hHBcode : HB.conjOperator Pi = M.secondCutCodeLift region := by
    simpa [HB, Pi] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hHBsector : HB.conjOperator ZB = M.secondCutSectorLift region bcomponent := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.secondCutCoordinateTransport region).symm).conjOperator ZB =
        M.secondCutSectorLift region bcomponent
    rw [composeUnitaryTransport_conjOperator]
    simpa [ZB, secondCutSectorLift] using
      M.secondCutCoordinateTransport_symm_conj_internalBoundaryLift region
        (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) bcomponent)
  have hBactiveTransport :
      HB.conjOperator Pi * HB.conjOperator ZB = HB.conjOperator Pi := by
    calc
      HB.conjOperator Pi * HB.conjOperator ZB =
          M.secondCutCodeLift region * M.secondCutSectorLift region bcomponent :=
        congrArg₂ (· * ·) hHBcode hHBsector
      _ = M.secondCutCodeLift region := hBactive
      _ = HB.conjOperator Pi := hHBcode.symm
  have hBphysical : Pi * ZB = Pi := by
    calc
      Pi * ZB = HB.symm.conjOperator (HB.conjOperator (Pi * ZB)) :=
        (HB.symm_conjOperator_conjOperator _).symm
      _ = HB.symm.conjOperator (HB.conjOperator Pi * HB.conjOperator ZB) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul]
      _ = HB.symm.conjOperator (HB.conjOperator Pi) :=
        congrArg HB.symm.conjOperator hBactiveTransport
      _ = Pi := HB.symm_conjOperator_conjOperator Pi
  let F := M.fourFactorTransport region
  have hjoint : Pi * ZB * ZC = Pi := by
    calc
      Pi * ZB * ZC = (Pi * ZB) * ZC := rfl
      _ = Pi * ZC := by rw [hBphysical]
      _ = Pi := hCphysical
  change F.conjOperator Pi * F.conjOperator ZB * F.conjOperator ZC = F.conjOperator Pi
  calc
    F.conjOperator Pi * F.conjOperator ZB * F.conjOperator ZC =
        F.conjOperator (Pi * ZB) * F.conjOperator ZC :=
      congrArg (fun operator => operator * F.conjOperator ZC)
        (Semantics.UnitaryTransport.conjOperator_mul F Pi ZB).symm
    _ = F.conjOperator (Pi * ZB * ZC) :=
      (Semantics.UnitaryTransport.conjOperator_mul F (Pi * ZB) ZC).symm
    _ = F.conjOperator Pi := congrArg F.conjOperator hjoint
end QEC.Bounds.BPTCommutingProjectorModel
