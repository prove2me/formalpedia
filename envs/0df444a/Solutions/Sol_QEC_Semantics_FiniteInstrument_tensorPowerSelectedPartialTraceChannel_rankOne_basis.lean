-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:07:01.682006+00:00
-- url     : https://prove2.me/submissions/7801bcfc-1662-4118-9da6-9f3ad91e82d3

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
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
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (left right : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
        required hrequired ι
        (InnerProductSpace.rankOne Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
            attempts left)
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
            attempts right)).toLinearMap =
      (inner Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory
                required hrequired ι).ComplementCoordinates)
            Complex
            (tensorPowerSelectedComplementBitstring accepts attempts
              observedHistory required hrequired ι right))
          (EuclideanSpace.basisFun
            (Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory
                required hrequired ι).ComplementCoordinates)
            Complex
            (tensorPowerSelectedComplementBitstring accepts attempts
              observedHistory required hrequired ι left))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι left))
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι right))).toLinearMap := by
  simp only [tensorPowerSelectedPartialTraceChannel,
    QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    tensorPowerQubitRegisterTransport_apply_basis,
    tensorPowerQubitRegisterTransport_apply_basis]
  simp only [FiniteSubsystem.selectedPartialTraceFromRegister,
    FiniteSubsystem.selectedPartialTrace, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne,
    FiniteSubsystem.registerFactorization_apply_basis,
    FiniteSubsystem.registerFactorization_apply_basis]
  change
    (tensorPowerSelectedRegisterReindex accepts attempts observedHistory required
      hrequired ι).conjOperator
      (partialTraceRightRaw
        (tensorPowerSelectedSubsystem accepts attempts observedHistory required
          hrequired ι).selectedSystem
        (tensorPowerSelectedSubsystem accepts attempts observedHistory required
          hrequired ι).complementSystem
        (InnerProductSpace.rankOne Complex
          (_ ⊗ₜ[Complex] _) (_ ⊗ₜ[Complex] _)).toLinearMap) = _
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  change
    (tensorPowerSelectedRegisterReindex accepts attempts observedHistory required
      hrequired ι).conjOperatorLinearMap (_ • _) = _
  rw [map_smul, UnitaryTransport.conjOperatorLinearMap_apply,
    QuditSubsystem.conjOperator_rankOne,
    tensorPowerSelectedRegisterReindex_apply_basis,
    tensorPowerSelectedRegisterReindex_apply_basis]
  rfl
end QEC.Semantics.FiniteInstrument
