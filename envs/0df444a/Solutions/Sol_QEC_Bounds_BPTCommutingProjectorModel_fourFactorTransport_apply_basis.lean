-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:22:49.335233+00:00
-- url     : https://prove2.me/submissions/bed62f65-ab9c-43fd-8006-5937d6f7bada

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedFactorization_apply_basis
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
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorTransport region
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.interior region)).selectedDimensions) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).1)
        ⊗ₜ[Complex]
      ((EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            ((M.regionSubsystem (M.interior region)).additionalRetainedDimensions
              (M.regionSubsystem region))) Complex
          ((M.regionSubsystem (M.interior region)).splitSelectedLabel
            (M.regionSubsystem region)
            (by
              intro site hsite
              exact (Finset.mem_sdiff.mp hsite).1)
            ((M.regionSubsystem region).splitLabel labels).1).2)
        ⊗ₜ[Complex]
        ((EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              ((M.regionSubsystem region).additionalRetainedDimensions
                (M.regionSubsystem (region ∪ M.externalBoundary region)))) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).1)
          ⊗ₜ[Complex]
          (EuclideanSpace.basisFun
            (Semantics.Qudit.Label
              (M.regionSubsystem (region ∪ M.externalBoundary region)).complementDimensions) Complex
            ((M.regionSubsystem region).splitComplementLabel
              (M.regionSubsystem (region ∪ M.externalBoundary region))
              (by
                intro site hsite
                exact Finset.mem_union_left _ hsite)
              ((M.regionSubsystem region).splitLabel labels).2).2))) := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  dsimp [fourFactorTransport]
  rw [nestedFactorizationLeft_apply_basis AB ABC hABABC]
  simp only [unitaryRTensor_apply_tmul]
  rw [A.selectedFactorization_apply_basis AB hAAB]
  simp only [tensorAssociatorUnitary_apply_tmul]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
