-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:30.793192+00:00
-- url     : https://prove2.me/submissions/c809d310-c02c-4183-adf9-8e39b153324f

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_apply_fourFactorBasisVector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundarySelectedToBCTransport_toLinearEquiv_apply_basis
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryToFourFactorReorder_toLinearEquiv_apply_tmul_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_quditCoordinateRelabel_apply_basis
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    (M.boundaryGlobalToFourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (M.fourFactorTransport region).toLinearEquiv
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    have hinternal : site ∈ M.internalBoundary region := hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hinternal
  have hBCABC : BC.selected ⊆ ABC.selected := by
    intro site hsite
    have hboundary : site ∈ M.boundary region := hsite
    change site ∈ region ∪ M.externalBoundary region
    rw [M.boundary_eq_internal_union_external region] at hboundary
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
    · exact Finset.mem_union_right _ hexternal
  rw [M.fourFactorTransport_apply_fourFactorBasisVector]
  simp only [boundaryGlobalToFourFactorTransport,
    composeUnitaryTransport_toLinearEquiv_apply]
  simp only [boundaryGlobalToMiddleTransport,
    composeUnitaryTransport_toLinearEquiv_apply]
  rw [BC.registerFactorization_apply_basis]
  simp only [unitaryRTensor_toLinearEquiv_apply_tmul,
    unitaryLTensor_toLinearEquiv_apply_tmul]
  dsimp only [BC]
  have hAD := M.boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
    region ((M.regionSubsystem (M.boundary region)).splitLabel labels).2
  refine (congrArg
    (fun vector : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorD region) =>
      (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          ((M.boundarySelectedToBCTransport region).toLinearEquiv
              (EuclideanSpace.basisFun
                (Semantics.Qudit.Label
                  (M.regionSubsystem (M.boundary region)).selectedDimensions) Complex
                ((M.regionSubsystem (M.boundary region)).splitLabel labels).1) ⊗ₜ[Complex]
            vector))) hAD).trans ?_
  have hBC := M.boundarySelectedToBCTransport_toLinearEquiv_apply_basis
    region ((M.regionSubsystem (M.boundary region)).splitLabel labels).1
  refine (congrArg
    (fun vector : Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region) =>
      (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          (vector ⊗ₜ[Complex]
            M.boundaryComplementToADBasisVector region
              ((M.regionSubsystem (M.boundary region)).splitLabel labels).2))) hBC).trans ?_
  unfold boundaryComplementToADBasisVector
  rw [M.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul_QECertChecked]
  dsimp [fourFactorBCoordinateRelabel]
  erw [quditCoordinateRelabel_apply_basis]
  erw [quditCoordinateRelabel_apply_basis]
  erw [quditCoordinateRelabel_apply_basis]
  unfold fourFactorBasisVector
  congr 1 <;> funext site <;> rfl
end QEC.Bounds.BPTCommutingProjectorModel
