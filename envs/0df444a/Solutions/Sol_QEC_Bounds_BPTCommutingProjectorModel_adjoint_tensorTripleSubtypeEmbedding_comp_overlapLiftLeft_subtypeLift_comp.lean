-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.adjoint_tensorTripleSubtypeEmbedding_comp_overlapLiftLeft_subtypeLift_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:35:50.548119+00:00
-- url     : https://prove2.me/submissions/d84cfee3-db52-4914-a31b-712a7cba278b

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_submoduleSubtype_comp_subtype_eq_one
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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (p : Submodule Complex B) (E : Semantics.Operator (Semantics.CompositeSystem A p)) :
    (LinearMap.adjoint (tensorTripleSubtypeEmbedding (A := A) (C := C) p)).comp
      ((overlapLiftLeft (C := C) (overlapLeftSubtypeLift p E)).comp
        (tensorTripleSubtypeEmbedding (A := A) (C := C) p)) =
      overlapLiftLeft (C := C) E := by
  let K : (Semantics.CompositeSystem A p) →ₗ[Complex]
      Semantics.CompositeSystem A B :=
    TensorProduct.map (1 : Semantics.Operator A) p.subtype
  let Kadj : (Semantics.CompositeSystem A B) →ₗ[Complex]
      Semantics.CompositeSystem A p :=
    TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint p.subtype)
  have hK : Kadj.comp K = (1 : Semantics.Operator (Semantics.CompositeSystem A p)) := by
    dsimp [K, Kadj]
    rw [← TensorProduct.map_comp]
    rw [adjoint_submoduleSubtype_comp_subtype_eq_one p]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id) LinearMap.id = LinearMap.id
    rw [LinearMap.id_comp]
    exact TensorProduct.map_one
  have hKadj : LinearMap.adjoint K = Kadj := by
    dsimp [K, Kadj]
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  let J := tensorTripleSubtypeEmbedding (A := A) (C := C) p
  have hJ : J = TensorProduct.map K (1 : Semantics.Operator C) := by rfl
  have hJadj : LinearMap.adjoint J = TensorProduct.map Kadj (1 : Semantics.Operator C) := by
    rw [hJ, TensorProduct.adjoint_map, hKadj, LinearMap.adjoint_one]
  have hLift : overlapLeftSubtypeLift p E = K.comp (E.comp Kadj) := by rfl
  change (LinearMap.adjoint J).comp
      ((overlapLiftLeft (C := C) (overlapLeftSubtypeLift p E)).comp J) =
      overlapLiftLeft (C := C) E
  rw [hJadj, hJ, hLift]
  unfold overlapLiftLeft
  rw [← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  congr 1
  calc
    Kadj.comp ((K.comp (E.comp Kadj)).comp K) =
        Kadj.comp (K.comp (E.comp (Kadj.comp K))) := by
      simp only [LinearMap.comp_assoc]
    _ = Kadj.comp (K.comp (E.comp (1 : Semantics.Operator (Semantics.CompositeSystem A p)))) := by
      rw [hK]
    _ = Kadj.comp (K.comp E) := by
      apply LinearMap.ext
      intro vector
      rfl
    _ = (Kadj.comp K).comp E := by rw [LinearMap.comp_assoc]
    _ = E := by rw [hK]; rfl
end QEC.Bounds.BPTCommutingProjectorModel
