-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.exteriorLocal_eq_regionComplementLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:44:23.182208+00:00
-- url     : https://prove2.me/submissions/86b28c02-47d6-4953-8031-f159800f8730

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_exteriorLocal_exists
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransportFromRegion_conj_extendComplementToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_eq_fourFactorTransportFromRegion
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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (P : Semantics.Operator (M.regionSubsystem (M.exterior region)).selectedSystem) :
    ∃ Z : Semantics.Operator (M.fourFactorD region),
      (M.regionSubsystem (M.exterior region)).extendLocalToRegister P =
        extendComplementToRegister (M.regionSubsystem region)
          (((M.regionSubsystem region).complementFactorization
            (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
              intro site hsite
              exact Finset.mem_union_left _ hsite)).symm.conjOperator
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
  rcases M.fourFactorTransport_conj_exteriorLocal_exists region P with ⟨Z, hExterior⟩
  let S := M.regionSubsystem region
  let T := M.regionSubsystem (region ∪ M.externalBoundary region)
  let splitCD := S.complementFactorization T (by
    intro site hsite
    exact Finset.mem_union_left _ hsite)
  let Q := splitCD.symm.conjOperator
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)
  have hComplement : (M.fourFactorTransport region).conjOperator
      (extendComplementToRegister S Q) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z)) := by
    rw [M.fourFactorTransport_eq_fourFactorTransportFromRegion]
    rw [M.fourFactorTransportFromRegion_conj_extendComplementToRegister]
    rw [show splitCD.conjOperator Q =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region)) Z by
      dsimp [Q]
      rw [splitCD.conjOperator_symm_conjOperator]]
    rfl
  refine ⟨Z, ?_⟩
  calc
    (M.regionSubsystem (M.exterior region)).extendLocalToRegister P =
        (M.fourFactorTransport region).symm.conjOperator
          ((M.fourFactorTransport region).conjOperator
            ((M.regionSubsystem (M.exterior region)).extendLocalToRegister P)) := by
              symm
              exact (M.fourFactorTransport region).symm_conjOperator_conjOperator _
    _ = (M.fourFactorTransport region).symm.conjOperator
        ((M.fourFactorTransport region).conjOperator (extendComplementToRegister S Q)) := by
          rw [hExterior, hComplement]
    _ = extendComplementToRegister S Q :=
      (M.fourFactorTransport region).symm_conjOperator_conjOperator _
end QEC.Bounds.BPTCommutingProjectorModel
