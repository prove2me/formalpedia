-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.externalResidual_scalar_compression_on_actual_active_sector_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:59:10.945918+00:00
-- url     : https://prove2.me/submissions/38a55fcd-1be2-4c9b-9a82-5e27f78b3f57

import Definitions.Def_QEC_Import_Compact_85e9be292dc002be
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_ExternalTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeIsometric_unitaryTransport_scalar_compression_of_intertwining
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_submoduleSubtype_comp_adjoint_eq_starProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_subtypeTensor_right_intertwines_zeroExtension
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap_left
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_left
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
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul_tmul
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
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.QEC.QECertImportCore.proof_85e9be292dc002be
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nC nB : Nat} [NeZero nC] [NeZero nB]
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC)))
    (Qsecond : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))))
    (Y : Semantics.Operator (WC.restrictScalars Complex))
    (E : Semantics.Operator (ccomponent.1.restrictScalars Complex))
    (Ephysical : Semantics.Operator (M.fourFactorC region)) (scalar : Complex)
    (hPullback : M.ExternalResidualProbePullback
      region ccomponent WC UC Y E Ephysical)
    (hQ : Qsecond.IsSymmetricProjection)
    (hsupport :
      Qsecond.comp
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
            (TensorProduct.map
              (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
              (1 : Semantics.Operator (M.fourFactorD region)))) = Qsecond)
    (hscalar : M.PhysicalExternalResidualProbeCompression
      region Qsecond Ephysical scalar) :
    M.ActualExternalResidualProbeCompression
      region ccomponent WC UC Qsecond Y scalar := by
  change M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nC))
            (1 : Semantics.Operator (M.fourFactorD region)))) *
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
    scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
  rcases hPullback with ⟨hE, hEphysical⟩
  change Qsecond *
      TensorProduct.map (1 : Semantics.Operator (isotypicLiftedMultiplicity.{0} nB))
        (TensorProduct.map Ephysical (1 : Semantics.Operator (M.fourFactorD region))) *
      Qsecond = scalar • Qsecond at hscalar
  let H := ccomponent.1.restrictScalars Complex
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let C := M.fourFactorC region
  let D := M.fourFactorD region
  let K : (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) →ₗ[Complex]
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map H.subtype (1 : Semantics.Operator D))
  let Kadj := LinearMap.adjoint K
  let V := composeUnitaryTransport (unitaryRTensor UC D)
    (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D)
  let Z : Semantics.Operator C :=
    leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent
  let S : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map Z (1 : Semantics.Operator D))
  have hsupport' : Qsecond.comp S = Qsecond := by
    simpa [S, Z, N, C, D] using hsupport
  have hKadj_eq : LinearMap.adjoint K = Kadj := rfl
  have hKKadj : K.comp Kadj = S := by
    dsimp [Kadj, K, S, Z]
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one,
      TensorProduct.adjoint_map, LinearMap.adjoint_one]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rw [submoduleSubtype_comp_adjoint_eq_starProjection H]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id)
      (TensorProduct.map H.starProjection.toLinearMap (LinearMap.id.comp LinearMap.id)) =
        TensorProduct.map LinearMap.id
          (TensorProduct.map
            (leftIsotypicSectorProjector (M.firstCutProjectorMC region) ccomponent)
            LinearMap.id)
    rw [LinearMap.id_comp, LinearMap.id_comp]
    rfl
  have hright : Qsecond.comp (K.comp Kadj) = Qsecond := by
    rw [hKKadj]
    exact hsupport'
  let R : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map Ephysical (1 : Semantics.Operator D))
  let Rsub : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem H D)) :=
    TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map E (1 : Semantics.Operator D))
  have hscalar' : Qsecond * R * Qsecond = scalar • Qsecond := by
    simpa [R, N, C, D] using hscalar
  have hintertwines : K.comp Rsub = R.comp K := by
    simpa [K, R, Rsub, N, H, C, D, hEphysical] using
      (subtypeTensor_right_intertwines_zeroExtension (N := N) (D := D)
        (ccomponent.1.restrictScalars Complex) E)
  have htransfer := activeIsometric_unitaryTransport_scalar_compression_of_intertwining
    K Kadj Qsecond R Rsub (unitaryLTensor N V) scalar
      hKadj_eq hQ hright hscalar' hintertwines
  have hEtransport : UC.conjOperator E =
      TensorProduct.map Y (1 : Semantics.Operator NC) := by
    rw [hE, UC.conjOperator_symm_conjOperator]
  have hVprobe : V.conjOperator
        (TensorProduct.map E (1 : Semantics.Operator D)) =
      TensorProduct.map Y
        (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D)) := by
    calc
      V.conjOperator (TensorProduct.map E (1 : Semantics.Operator D)) =
          (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
            ((unitaryRTensor UC D).conjOperator
              (TensorProduct.map E (1 : Semantics.Operator D))) := by
        simpa only [V] using
          composeUnitaryTransport_conjOperator (unitaryRTensor UC D)
            (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D)
            (TensorProduct.map E (1 : Semantics.Operator D))
      _ = (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
          (TensorProduct.map (UC.conjOperator E) (1 : Semantics.Operator D)) :=
        congrArg
          (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
          (unitaryRTensor_conj_tensorMap_left UC D E)
      _ = (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
          (TensorProduct.map
            (TensorProduct.map Y (1 : Semantics.Operator NC))
            (1 : Semantics.Operator D)) :=
        congrArg
          (fun operator =>
            (tensorAssociatorUnitary (WC.restrictScalars Complex) NC D).conjOperator
              (TensorProduct.map operator (1 : Semantics.Operator D)))
          hEtransport
      _ = TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D)) :=
        tensorAssociatorUnitary_conj_tensorMap Y
          (1 : Semantics.Operator NC) (1 : Semantics.Operator D)
  have hTprobe : (unitaryLTensor N V).conjOperator Rsub =
      TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) := by
    calc
      (unitaryLTensor N V).conjOperator Rsub =
          TensorProduct.map (1 : Semantics.Operator N)
            (V.conjOperator (TensorProduct.map E (1 : Semantics.Operator D))) := by
        simpa only [Rsub] using
        unitaryLTensor_conj_tensorMap_left N V
          (TensorProduct.map E (1 : Semantics.Operator D))
      _ = TensorProduct.map (1 : Semantics.Operator N)
          (TensorProduct.map Y
            (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) :=
        congrArg (TensorProduct.map (1 : Semantics.Operator N)) hVprobe
  have hactiveBlock :
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
        (unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) := by
    rfl
  have hleftProduct :
      M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
          TensorProduct.map (1 : Semantics.Operator N)
            (TensorProduct.map Y
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) =
        (unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) *
          (unitaryLTensor N V).conjOperator Rsub :=
    congrArg₂ (fun left right => left * right) hactiveBlock hTprobe.symm
  calc
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond *
          TensorProduct.map (1 : Semantics.Operator N)
            (TensorProduct.map Y
              (TensorProduct.map (1 : Semantics.Operator NC) (1 : Semantics.Operator D))) *
        M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond =
      ((unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) *
        (unitaryLTensor N V).conjOperator Rsub) *
        (unitaryLTensor N V).conjOperator (Kadj.comp (Qsecond.comp K)) :=
      congrArg₂ (fun left right => left * right) hleftProduct hactiveBlock
    _ = scalar • (unitaryLTensor N V).conjOperator
        (Kadj.comp (Qsecond.comp K)) := htransfer
    _ = scalar • M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond :=
      congrArg (fun operator => scalar • operator) hactiveBlock.symm
end QEC.Bounds.BPTCommutingProjectorModel

end

universe checked_u0
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.externalResidual_scalar_compression_on_actual_active_sector_QECertStatement.{checked_u0} := @QEC.QECertImportCore.proof_85e9be292dc002be.{checked_u0}
