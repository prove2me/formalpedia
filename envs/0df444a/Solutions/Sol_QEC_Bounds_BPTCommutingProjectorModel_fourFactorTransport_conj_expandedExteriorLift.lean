-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_expandedExteriorLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:37:14.459002+00:00
-- url     : https://prove2.me/submissions/6de0e5fe-fc6c-43f0-b24d-a6ca20dedc6e

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_eq_fourFactorTransportFromNestedRegion
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_right
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_ext
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
set_option maxHeartbeats 1000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorD region)) :
    (M.fourFactorTransport region).conjOperator
      (extendComplementToRegister
        (M.regionSubsystem (region ∪ M.externalBoundary region)) Z) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact { toLinearEquiv := e.toLinearEquiv, map_inner := e.map_inner }
  let nested := nestedFactorizationRight AB ABC hABABC
  have hnested : nested =
      composeUnitaryTransport
        (composeUnitaryTransport ABC.registerFactorization
          (unitaryRTensor (AB.selectedFactorization ABC hABABC) ABC.complementSystem))
        (tensorAssociatorUnitary AB.selectedSystem
          (AB.additionalRetainedSystem ABC) ABC.complementSystem) := by
    apply unitaryTransport_ext
    rfl
  have hfirst : nested.conjOperator
      (extendComplementToRegister ABC Z) =
      TensorProduct.map (1 : Semantics.Operator AB.selectedSystem)
        (TensorProduct.map
          (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z) := by
    rw [hnested, composeUnitaryTransport_conjOperator,
      composeUnitaryTransport_conjOperator]
    unfold extendComplementToRegister
    rw [ABC.registerFactorization.conjOperator_symm_conjOperator]
    rw [unitaryRTensor_conj_tensorMap_right]
    rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem AB.selectedSystem
        (AB.additionalRetainedSystem ABC))) =
        TensorProduct.map (1 : Semantics.Operator AB.selectedSystem)
          (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) by
      symm
      exact TensorProduct.map_one]
    exact tensorAssociatorUnitary_conj_tensorMap
      (1 : Semantics.Operator AB.selectedSystem)
      (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z
  calc
    (M.fourFactorTransport region).conjOperator
        (extendComplementToRegister ABC Z) =
      (M.fourFactorTransportFromNestedRegion region).conjOperator
        (extendComplementToRegister ABC Z) := by
          exact congrArg (fun transport => transport.conjOperator
            (extendComplementToRegister ABC Z))
            (M.fourFactorTransport_eq_fourFactorTransportFromNestedRegion region)
    _ = (tensorAssociatorUnitary A.selectedSystem
        (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
          ABC.complementSystem)).conjOperator
        ((unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
            ABC.complementSystem)).conjOperator
          (nested.conjOperator (extendComplementToRegister ABC Z))) := by
          dsimp [fourFactorTransportFromNestedRegion]
          rw [composeUnitaryTransport_conjOperator,
            composeUnitaryTransport_conjOperator]
    _ = (tensorAssociatorUnitary A.selectedSystem
        (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
          ABC.complementSystem)).conjOperator
        ((unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC)
            ABC.complementSystem)).conjOperator
          (TensorProduct.map (1 : Semantics.Operator AB.selectedSystem)
            (TensorProduct.map
              (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z))) := by
          rw [hfirst]
    _ = TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
          (TensorProduct.map (1 : Semantics.Operator (A.additionalRetainedSystem AB))
          (TensorProduct.map (1 : Semantics.Operator (AB.additionalRetainedSystem ABC)) Z)) := by
          rw [unitaryRTensor_conj_tensorMap_right]
          rw [show (1 : Semantics.Operator
            (Semantics.CompositeSystem A.selectedSystem
              (A.additionalRetainedSystem AB))) =
              TensorProduct.map (1 : Semantics.Operator A.selectedSystem)
                (1 : Semantics.Operator (A.additionalRetainedSystem AB)) by
              symm
              exact TensorProduct.map_one]
          exact tensorAssociatorUnitary_conj_tensorMap
            (1 : Semantics.Operator A.selectedSystem)
            (1 : Semantics.Operator (A.additionalRetainedSystem AB))
            (TensorProduct.map (1 : Semantics.Operator
              (AB.additionalRetainedSystem ABC)) Z)
end QEC.Bounds.BPTCommutingProjectorModel
