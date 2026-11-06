-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_comp_tensorMap_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:03:47.566208+00:00
-- url     : https://prove2.me/submissions/290ea209-baf4-458f-8d41-f0ab8430ea5a

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A A' H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup A'] [InnerProductSpace Complex A'] [Semantics.FiniteQuantumSystem A']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (K : A →ₗ[Complex] A') :
    (isotypicSectorBlockTransportLeft A' H W N C U).toLinearEquiv.toLinearMap.comp
        (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator H))
          (1 : Semantics.Operator C)) =
      (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator W))
        (1 : Semantics.Operator (Semantics.CompositeSystem N C))).comp
        (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv.toLinearMap := by
  have hAssocSymm :
      ((tensorAssociatorUnitary A' W (Semantics.CompositeSystem N C)).symm.toLinearEquiv.toLinearMap).comp
          (TensorProduct.map K
            (1 : Semantics.Operator (Semantics.CompositeSystem W
              (Semantics.CompositeSystem N C)))) =
        (TensorProduct.map (TensorProduct.map K (1 : Semantics.Operator W))
          (1 : Semantics.Operator (Semantics.CompositeSystem N C))).comp
          (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul a wnc =>
        induction wnc using TensorProduct.induction_on with
        | zero => simp
        | tmul w nc => rfl
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.tmul_add, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  apply LinearMap.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul ah c =>
      induction ah using TensorProduct.induction_on with
      | zero => simp
      | tmul a h =>
          let z : Semantics.CompositeSystem W N := U.toLinearEquiv h
          have hfinal := congrArg (fun map =>
              map (a ⊗ₜ[Complex]
                (TensorProduct.assoc Complex W N C) (z ⊗ₜ[Complex] c))) hAssocSymm
          simpa [isotypicSectorBlockTransportLeft, composeUnitaryTransport,
            unitaryRTensor, unitaryLTensor, tensorAssociatorUnitary, z,
            LinearMap.comp_apply] using hfinal
      | add first second hfirst hsecond =>
          simpa only [TensorProduct.add_tmul, map_add] using
            congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
end QEC.Bounds.BPTCommutingProjectorModel
