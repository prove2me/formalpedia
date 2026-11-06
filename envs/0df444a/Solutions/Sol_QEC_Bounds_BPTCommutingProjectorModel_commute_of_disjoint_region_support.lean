-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.commute_of_disjoint_region_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:10:16.865326+00:00
-- url     : https://prove2.me/submissions/1243ede7-d7c2-4c2d-a1c8-53cedcaf933d

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_complement_eq_extendComplementToRegister
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
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    {A B : Semantics.Operator L.Register}
    (hA : (M.regionSubsystem left).OperatorSupportedOnRegister A)
    (hB : (M.regionSubsystem right).OperatorSupportedOnRegister B) :
    Commute A B := by
  rcases hA with ⟨localA, hlocalA⟩
  have hrightComplement : right ⊆ leftᶜ := by
    intro site hright
    exact Finset.mem_compl.mpr (fun hleft =>
      (Finset.disjoint_left.mp hdisjoint) hleft hright)
  have hBComplement :
      (M.regionSubsystem leftᶜ).OperatorSupportedOnRegister B := by
    apply operatorSupportedOnRegister_of_subset (M.regionSubsystem right)
      (M.regionSubsystem leftᶜ)
    · simpa [BPTCommutingProjectorModel.regionSubsystem] using hrightComplement
    · exact hB
  rcases hBComplement with ⟨localB, hlocalB⟩
  let S := M.regionSubsystem left
  let relabel := M.regionComplementCoordinateRelabel left
  have hcomplement :
      B = extendComplementToRegister S (relabel.conjOperator localB) := by
    calc
      B = (M.regionSubsystem leftᶜ).extendLocalToRegister localB := hlocalB.symm
      _ = extendComplementToRegister S (relabel.conjOperator localB) := by
        simpa [S, relabel] using
          (M.extendLocalToRegister_complement_eq_extendComplementToRegister left localB)
  rw [← hlocalA, hcomplement]
  change
    S.registerFactorization.symm.conjOperator
        (TensorProduct.map localA (1 : Semantics.Operator S.complementSystem)) *
      S.registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
          (relabel.conjOperator localB)) =
    S.registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator S.selectedSystem)
          (relabel.conjOperator localB)) *
      S.registerFactorization.symm.conjOperator
        (TensorProduct.map localA (1 : Semantics.Operator S.complementSystem))
  rw [← Semantics.UnitaryTransport.conjOperator_mul,
    ← Semantics.UnitaryTransport.conjOperator_mul]
  congr 1
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
  simp
end QEC.Bounds.BPTCommutingProjectorModel
