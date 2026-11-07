-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_all_externalLocal_scalar_compression_of_externalBoundary_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:16.268971+00:00
-- url     : https://prove2.me/submissions/8da4533a-7149-4e20-89f4-9bfff3d81500

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_externalBoundaryLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_implies_noInformationOn
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
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
set_option maxHeartbeats 2000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (E : Semantics.Operator (M.fourFactorC region)) :
    ∃ scalar : Complex,
      M.secondCutCodeLift region *
          TensorProduct.map
            (1 : Semantics.Operator
              (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)))
            (TensorProduct.map E (1 : Semantics.Operator (M.fourFactorD region))) *
          M.secondCutCodeLift region = scalar • M.secondCutCodeLift region := by
  let S := M.regionSubsystem (M.externalBoundary region)
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let AB := Semantics.CompositeSystem A B
  let D := M.fourFactorD region
  let Elocal : Semantics.Operator S.selectedSystem :=
    (M.fourFactorCCoordinateRelabel region).symm.conjOperator E
  let Ephysical : Semantics.Operator L.Register := S.extendLocalToRegister Elocal
  let G := M.secondCutGlobalCoordinateTransport region
  let R := M.secondCutCodeLift region
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn
    (M.externalBoundary region) hC
  have hAll := (S.noInformationOn_iff_allLocalScalarCompression M.codeSpace).mp hInformation
  rcases hAll Elocal with ⟨scalar, hscalar⟩
  have hscalar' : M.fullCodeProjector * Ephysical * M.fullCodeProjector =
      scalar • M.fullCodeProjector := by
    change (M.fullCodeProjector.comp Ephysical).comp M.fullCodeProjector = _
    rw [LinearMap.comp_assoc]
    exact hscalar
  have hGcode : G.conjOperator M.fullCodeProjector = R := by
    simpa [G, R] using M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector region
  have hGlocal : G.conjOperator Ephysical =
      TensorProduct.map (1 : Semantics.Operator AB)
        (TensorProduct.map E (1 : Semantics.Operator D)) := by
    let U := M.secondCutCoordinateTransport region
    have hfour : (M.fourFactorTransport region).conjOperator Ephysical =
        TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map (1 : Semantics.Operator B)
            (TensorProduct.map E (1 : Semantics.Operator D))) := by
      simpa [Ephysical, Elocal] using
        M.fourFactorTransport_conj_externalBoundaryLift region E
    have hsecond : U.conjOperator
        (TensorProduct.map (1 : Semantics.Operator AB)
          (TensorProduct.map E (1 : Semantics.Operator D))) =
        TensorProduct.map (1 : Semantics.Operator A)
          (TensorProduct.map (1 : Semantics.Operator B)
            (TensorProduct.map E (1 : Semantics.Operator D))) := by
      change (tensorAssociatorUnitary A B
        (Semantics.CompositeSystem (M.fourFactorC region) D)).conjOperator
          (TensorProduct.map (1 : Semantics.Operator AB)
            (TensorProduct.map E (1 : Semantics.Operator D))) = _
      rw [show (1 : Semantics.Operator AB) =
          TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator B) by
        symm
        exact TensorProduct.map_one]
      exact tensorAssociatorUnitary_conj_tensorMap
        (1 : Semantics.Operator A) (1 : Semantics.Operator B)
        (TensorProduct.map E (1 : Semantics.Operator D))
    calc
      G.conjOperator Ephysical =
          U.symm.conjOperator ((M.fourFactorTransport region).conjOperator Ephysical) := by
        simpa only [G, U, secondCutGlobalCoordinateTransport] using
          (composeUnitaryTransport_conjOperator (M.fourFactorTransport region)
            (M.secondCutCoordinateTransport region).symm Ephysical)
      _ =
          U.symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator A)
              (TensorProduct.map (1 : Semantics.Operator B)
                (TensorProduct.map E (1 : Semantics.Operator D)))) :=
        congrArg U.symm.conjOperator hfour
      _ = U.symm.conjOperator
          (U.conjOperator
            (TensorProduct.map (1 : Semantics.Operator AB)
              (TensorProduct.map E (1 : Semantics.Operator D)))) :=
        congrArg U.symm.conjOperator hsecond.symm
      _ = TensorProduct.map (1 : Semantics.Operator AB)
          (TensorProduct.map E (1 : Semantics.Operator D)) :=
        U.symm_conjOperator_conjOperator _
  refine ⟨scalar, ?_⟩
  calc
    R * TensorProduct.map (1 : Semantics.Operator AB)
        (TensorProduct.map E (1 : Semantics.Operator D)) * R =
        G.conjOperator M.fullCodeProjector * G.conjOperator Ephysical *
          G.conjOperator M.fullCodeProjector := by
      rw [hGcode, hGlocal]
    _ = G.conjOperator (M.fullCodeProjector * Ephysical * M.fullCodeProjector) := by
      rw [Semantics.UnitaryTransport.conjOperator_mul,
        Semantics.UnitaryTransport.conjOperator_mul]
    _ = G.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg G.conjOperator hscalar'
    _ = scalar • G.conjOperator M.fullCodeProjector := by
      exact G.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector
    _ = scalar • R := congrArg (fun operator => scalar • operator) hGcode
    _ = scalar • M.secondCutCodeLift region := rfl
end QEC.Bounds.BPTCommutingProjectorModel
