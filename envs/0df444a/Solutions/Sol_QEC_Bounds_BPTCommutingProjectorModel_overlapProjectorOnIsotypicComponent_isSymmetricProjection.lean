-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlapProjectorOnIsotypicComponent_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:43:31.888058+00:00
-- url     : https://prove2.me/submissions/b7692b0a-cbd8-418c-b8fc-4ab7780b314c

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_isometric_compression_commuting
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_submoduleSubtype_comp_subtype_eq_one
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_leftOverlap_of_commute_leftInteractionCoefficients
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commute_leftInteractionCoefficient
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_submoduleSubtype_comp_adjoint_eq_starProjection
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
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (hP : P.IsSymmetricProjection)
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (overlapProjectorOnIsotypicComponent P component).IsSymmetricProjection := by
  let p : Submodule Complex B := component.1.restrictScalars Complex
  let J : (Semantics.CompositeSystem A p) →ₗ[Complex]
      Semantics.CompositeSystem A B :=
    TensorProduct.map (1 : Semantics.Operator A) p.subtype
  let Jadj : (Semantics.CompositeSystem A B) →ₗ[Complex]
      Semantics.CompositeSystem A p :=
    TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint p.subtype)
  have hJadj : Jadj.comp J = (1 : Semantics.Operator (Semantics.CompositeSystem A p)) := by
    dsimp [J, Jadj]
    rw [← TensorProduct.map_comp]
    rw [adjoint_submoduleSubtype_comp_subtype_eq_one p]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id) LinearMap.id = LinearMap.id
    rw [LinearMap.id_comp]
    exact TensorProduct.map_one
  have hJadj_eq : LinearMap.adjoint J = Jadj := by
    dsimp [J, Jadj]
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  have hJJ : J.comp Jadj =
      TensorProduct.map (1 : Semantics.Operator A)
        (leftIsotypicSectorProjector P component) := by
    dsimp [J, Jadj]
    rw [← TensorProduct.map_comp]
    rw [submoduleSubtype_comp_adjoint_eq_starProjection p]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id) p.starProjection.toLinearMap =
      TensorProduct.map LinearMap.id (leftIsotypicSectorProjector P component)
    rw [LinearMap.id_comp]
    rfl
  have hsectorCommutes : Commute P
      (TensorProduct.map (1 : Semantics.Operator A)
        (leftIsotypicSectorProjector P component)) := by
    apply commute_leftOverlap_of_commute_leftInteractionCoefficients
    intro a a'
    exact leftIsotypicSectorProjector_commute_leftInteractionCoefficient P component a a'
  have hcommute : Commute P (J.comp Jadj) := by
    rw [hJJ]
    exact hsectorCommutes
  change (Jadj.comp (P.comp J)).IsSymmetricProjection
  exact isSymmetricProjection_of_isometric_compression_commuting
    J Jadj P hJadj hJadj_eq hP hcommute
end QEC.Bounds.BPTCommutingProjectorModel
