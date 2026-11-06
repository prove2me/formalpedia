-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryComplementToADTransport_toLinearEquiv_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:51:14.189967+00:00
-- url     : https://prove2.me/submissions/34be74a0-98fc-4083-849a-357dc590a7e7

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_complementFactorization_apply_basis
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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    (M.boundaryComplementToADTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).complementDimensions) Complex labels) =
      (quditCoordinateRelabel
          (q := (M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
            (M.regionSubsystem (region ∪ M.externalBoundary region)))
          (r := (M.regionSubsystem (M.interior region)).selectedDimensions)
          (M.boundaryComplementAdditionalCoordinateEquiv region) (by
            intro site
            rfl))
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.boundary region)).additionalRetainedDimensions
              (M.regionSubsystem (region ∪ M.externalBoundary region))))
          Complex
          ((M.regionSubsystem (M.boundary region)).splitComplementLabel
            (M.regionSubsystem (region ∪ M.externalBoundary region))
            (by
              intro site hsite
              change site ∈ region ∪ M.externalBoundary region
              rw [M.boundary_eq_internal_union_external region] at hsite
              rcases Finset.mem_union.mp hsite with hinternal | hexternal
              · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
              · exact Finset.mem_union_right _ hexternal)
            labels).1) ⊗ₜ[Complex]
      EuclideanSpace.basisFun
        (Semantics.Qudit.Label
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
        ((M.regionSubsystem (M.boundary region)).splitComplementLabel
          (M.regionSubsystem (region ∪ M.externalBoundary region))
          (by
            intro site hsite
            change site ∈ region ∪ M.externalBoundary region
            rw [M.boundary_eq_internal_union_external region] at hsite
            rcases Finset.mem_union.mp hsite with hinternal | hexternal
            · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
            · exact Finset.mem_union_right _ hexternal)
          labels).2 := by
  let BC := M.regionSubsystem (M.boundary region)
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hBCABC : BC.selected ⊆ ABC.selected := by
    intro site hsite
    have hboundary : site ∈ M.boundary region := hsite
    change site ∈ region ∪ M.externalBoundary region
    rw [M.boundary_eq_internal_union_external region] at hboundary
    rcases Finset.mem_union.mp hboundary with hinternal | hexternal
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hinternal).2
    · exact Finset.mem_union_right _ hexternal
  dsimp [boundaryComplementToADTransport]
  rw [BC.complementFactorization_apply_basis ABC hBCABC]
  simp only [composeUnitaryTransport_toLinearEquiv_apply,
    unitaryRTensor_toLinearEquiv_apply_tmul]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
