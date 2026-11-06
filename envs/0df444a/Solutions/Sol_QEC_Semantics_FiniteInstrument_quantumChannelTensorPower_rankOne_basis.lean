-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:27:24.710193+00:00
-- url     : https://prove2.me/submissions/a2ec73b8-a2a6-497c-ac40-d0320ab8e400

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryAt_map
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_inducedMap_tensorMap
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
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


attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerHistoryAt_map

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {beta gamma : Type u} [Fintype beta] [Fintype gamma]
    (channel : QuantumChannel H K)
    (sourceBasis : OrthonormalBasis beta Complex H)
    (targetBasis : OrthonormalBasis gamma Complex K)
    (mapIndex : beta → gamma)
    (coefficient : beta → beta → Complex)
    (haction : ∀ left right,
      channel
          (InnerProductSpace.rankOne Complex
            (sourceBasis left) (sourceBasis right)).toLinearMap =
        coefficient left right •
          (InnerProductSpace.rankOne Complex
            (targetBasis (mapIndex left))
            (targetBasis (mapIndex right))).toLinearMap) :
    ∀ attempts
      (left right : tensorPowerHistory beta attempts),
      quantumChannelTensorPower channel attempts
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis sourceBasis attempts left)
            (tensorPowerBasis sourceBasis attempts right)).toLinearMap =
        (∏ trial : Fin attempts,
          coefficient
            (tensorPowerHistoryAt beta attempts left trial)
            (tensorPowerHistoryAt beta attempts right trial)) •
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis targetBasis attempts
              (tensorPowerHistoryMap mapIndex attempts left))
            (tensorPowerBasis targetBasis attempts
              (tensorPowerHistoryMap mapIndex attempts right))).toLinearMap := by
  intro attempts
  induction attempts with
  | zero =>
      intro left right
      cases left
      cases right
      simp only [quantumChannelTensorPower, FiniteKrausFamily.toQuantumChannel_apply]
      change tensorUnitInstrument.{u, 0, 0}.kraus.inducedMap
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis sourceBasis 0 PUnit.unit)
          (tensorPowerBasis sourceBasis 0 PUnit.unit)).toLinearMap = _
      rw [FiniteKrausFamily.inducedMap_apply]
      simp only [tensorUnitInstrument, Fintype.sum_unique, LinearMap.adjoint_one,
        Module.End.one_eq_id, LinearMap.adjoint_id, LinearMap.id_comp, LinearMap.comp_id,
        Fin.prod_univ_zero, one_smul]
      rfl
  | succ attempts ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      simp only [quantumChannelTensorPower,
        FiniteKrausFamily.toQuantumChannel_apply]
      rw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
      rw [← DensityOperator.tensorMap_rankOne]
      change
        (channel.toFiniteInstrument.tensor
          (channel.toFiniteInstrument.tensorPower attempts)).kraus.inducedMap
            (TensorProduct.map
              (InnerProductSpace.rankOne Complex
                (sourceBasis leftHead) (sourceBasis rightHead)).toLinearMap
              (InnerProductSpace.rankOne Complex
                (tensorPowerBasis sourceBasis attempts leftTail)
                (tensorPowerBasis sourceBasis attempts rightTail)).toLinearMap) = _
      refine (tensor_inducedMap_tensorMap
        channel.toFiniteInstrument
        (channel.toFiniteInstrument.tensorPower attempts) _ _).trans ?_
      rw [QuantumChannel.toFiniteInstrument_inducedMap_apply]
      rw [haction leftHead rightHead]
      change TensorProduct.map
          (coefficient leftHead rightHead •
            (InnerProductSpace.rankOne Complex
              (targetBasis (mapIndex leftHead))
              (targetBasis (mapIndex rightHead))).toLinearMap)
          (quantumChannelTensorPower channel attempts
            (InnerProductSpace.rankOne Complex
              (tensorPowerBasis sourceBasis attempts leftTail)
              (tensorPowerBasis sourceBasis attempts rightTail)).toLinearMap) = _
      rw [ih leftTail rightTail]
      rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right,
        smul_smul]
      rw [DensityOperator.tensorMap_rankOne]
      rw [Fin.prod_univ_succ]
      simp only [tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ,
        tensorPowerHistoryMap]
      erw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
end QEC.Semantics.FiniteInstrument
