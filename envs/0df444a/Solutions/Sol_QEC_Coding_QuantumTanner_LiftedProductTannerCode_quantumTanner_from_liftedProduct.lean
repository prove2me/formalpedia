-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerCode.quantumTanner_from_liftedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:43:41.339046+00:00
-- url     : https://prove2.me/submissions/17cb8c5f-5cb3-4f6a-9235-be7077283672

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerCode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selected_lifted_product_eq_quantum_tanner
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerCode
open Classical LiftedProductTannerBridge LiftedProductTensorBridge
open LiftedProductActionBridge LiftedProductRestriction
variable {G A B : Type} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {C D C' D' : Type} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']
namespace QEC.Coding.QuantumTanner.LiftedProductTannerCode
theorem _root_.solution
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (bridgeLeft : A → G) (bridgeRight : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, bridgeLeft (invA i) = (bridgeLeft i)⁻¹) (hInvB : ∀ j, bridgeRight (invB j) = (bridgeRight j)⁻¹)
    (hDualA : _root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA) =
      (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : _root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gB) =
      (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let lifted : _root_.QEC.Coding.LiftedProduct.Data (ZMod 2) G (Bool × D) B A (Bool × C) :=
      LiftedProductActionBridge.canonicalData hA hB bridgeLeft bridgeRight
    let tanner : _root_.QEC.Coding.QuantumTanner.Data (VertexGroup G) A B (A × B × G)
        (Fin (Dimension (tensorCode (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA)).dual
          (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB)).dual)))
        (Fin (Dimension (tensorCode (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
          (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))))) :=
      selectedData hA hB gA gB bridgeLeft bridgeRight invA invB hInvA hInvB hDualA hDualB
    Set.range (fun U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
        Matrix C D' (MonoidAlgebra (ZMod 2) G) => fun (i, j, g) =>
      (LiftedProduct.boundary2Matrix lifted).mulVec
        (zParameter (U.1 * twistedMatrix gB (fun j => (bridgeRight j)⁻¹)) (U.2 * scalarMatrix gB))
        (retainedCoordinate i j g)) = (LinearMap.range tanner.toRawData.zGeneratorMap).carrier ∧
    Set.range (fun V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
        Matrix C' D (MonoidAlgebra (ZMod 2) G) => fun (i, j, g) =>
      (LiftedProduct.boundary1Matrix lifted).transpose.mulVec
        (xParameter ((scalarMatrix gA).transpose * V.1)
          ((twistedMatrix gA (fun i => (bridgeLeft i)⁻¹)).transpose * V.2))
        (retainedCoordinate i j g)) = (LinearMap.range tanner.toRawData.xGeneratorMap).carrier ∧
    tanner.blockLength = Fintype.card G * Fintype.card A * Fintype.card B := by
  dsimp only
  change Set.range (selectedZWord hA hB gB bridgeLeft bridgeRight) = _ ∧
    Set.range (selectedXWord hA hB gA bridgeLeft bridgeRight) = _ ∧ _
  have hSpaces := selected_lifted_product_eq_quantum_tanner hA hB gA gB bridgeLeft bridgeRight hDualA hDualB
  refine ⟨?_, ?_, ?_⟩
  · change Set.range (selectedZWord hA hB gB bridgeLeft bridgeRight) =
      (LinearMap.range (coverRawData bridgeLeft bridgeRight invA invB hInvA hInvB
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))).zGeneratorMap).carrier
    rw [coverRawData_z_range]
    exact hSpaces.1
  · change Set.range (selectedXWord hA hB gA bridgeLeft bridgeRight) =
      (LinearMap.range (coverRawData bridgeLeft bridgeRight invA invB hInvA hInvB
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))).xGeneratorMap).carrier
    rw [coverRawData_x_range]
    exact hSpaces.2.1
  · simp [Data.blockLength, Fintype.card_prod, mul_assoc, mul_left_comm, mul_comm]
end QEC.Coding.QuantumTanner.LiftedProductTannerCode
