-- Prove2me | solution 1 for QEC.Locality.partialTraceRightRaw_split_eq_compression_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:32.972006+00:00
-- url     : https://prove2.me/submissions/68fe1c57-2d98-4a0a-82e1-f80c2acd0b31

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_tensorRight_adjoint_tmul
import Theorems.Thm_QEC_Locality_dual_apply_sum_basis
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    ((dualTensorHomEquiv Complex H H).toLinearMap.comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap)))
      =
    (rightCompression H K b).comp
      ((dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).toLinearMap.comp
        (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
          (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap) := by
  apply TensorProduct.ext
  ext φ ψ h k z
  simp [rightCompression, tensorRight_adjoint_tmul, LinearMap.comp_apply,
    dualTensorHomEquiv, dualTensorHom_apply]
  rw [← dual_apply_sum_basis H K b ψ k]
  simp [tensorRight, Finset.mul_sum, Finset.sum_smul, mul_comm, mul_assoc, smul_smul]
end QEC.Locality
