-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:55:21.868207+00:00
-- url     : https://prove2.me/submissions/3a9ae863-d842-4fa0-a869-a78680be8d6b

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceRightRaw_trace_pairing
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_operator_ext_of_trace_comp_right_eq
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
universe u
namespace QEC
namespace Semantics
open scoped TensorProduct
noncomputable section
namespace FiniteInstrument
private theorem partialTraceRightRaw_tensorMap
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K) :
    partialTraceRightRaw H K (TensorProduct.map A B) =
      (LinearMap.trace Complex K B) • A := by
  apply operator_ext_of_trace_comp_right_eq
  intro X
  let basis : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex K))) Complex K :=
    (stdOrthonormalBasis Complex K).reindex Equiv.ulift.symm
  calc
    LinearMap.trace Complex H
          (X.comp (partialTraceRightRaw H K (TensorProduct.map A B))) =
        LinearMap.trace Complex H
          ((partialTraceRightRaw H K (TensorProduct.map A B)).comp X) :=
      (LinearMap.trace_comp_comm' X
        (partialTraceRightRaw H K (TensorProduct.map A B))).symm
    _ = LinearMap.trace Complex (CompositeSystem H K)
          ((TensorProduct.map A B).comp
            (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))) :=
      FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
        basis (TensorProduct.map A B) X
    _ = LinearMap.trace Complex H
          (((LinearMap.trace Complex K B) • A).comp X) := by
      rw [← TensorProduct.map_comp, LinearMap.trace_tensorProduct']
      simp [LinearMap.smul_comp]
      ring
    _ = LinearMap.trace Complex H
          (X.comp ((LinearMap.trace Complex K B) • A)) :=
      LinearMap.trace_comp_comm' X ((LinearMap.trace Complex K B) • A)
end FiniteInstrument
end
end Semantics
end QEC
end

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    partialTraceRightRaw_mapDensity H K
        (DensityOperator.tensorDensity rho sigma) = rho := by
  apply DensityOperator.ext_toOperator
  simp only [partialTraceRightRaw_mapDensity_toOperator,
    DensityOperator.tensorDensity_toOperator]
  rw [partialTraceRightRaw_tensorMap, sigma.trace_one]
  simp
end QEC.Semantics.FiniteInstrument
