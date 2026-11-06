-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_matrixEntry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:11:36.97178+00:00
-- url     : https://prove2.me/submissions/7e280abc-65a3-41c8-a0ff-acab24db06a5

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
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
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι A
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        inner Complex
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
              required hrequired ι).symm (left, complement)))
          (A
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
              ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
                required hrequired ι).symm (right, complement)))) := by
  rw [tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion]
  simp only [LinearMap.sum_apply]
  rw [inner_sum]
  simp_rw [inner_sum]
  have hRankOne (outputLeft outputRight : Qubit.Bitstring (Fin required × ι)) :
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
          outputLeft)
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
          outputRight)).toLinearMap
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            right) =
        inner Complex
            (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
              outputRight)
            (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
              right) •
          EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            outputLeft := by
    rfl
  simp only [LinearMap.smul_apply, inner_smul_right]
  simp_rw [hRankOne]
  simp only [inner_smul_right]
  let inputBasis :=
    tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
  let outputBasis :=
    EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
  let complementBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts observedHistory required
          hrequired ι).ComplementCoordinates)
      Complex
  let splitEquiv :=
    tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
      required hrequired ι
  let entryTerm := fun
      (rightHistory leftHistory : tensorPowerHistory (Qubit.Bitstring ι) attempts) =>
    inner Complex (inputBasis leftHistory) (A (inputBasis rightHistory)) *
      inner Complex
        (complementBasis
          (tensorPowerSelectedComplementBitstring accepts attempts observedHistory
            required hrequired ι rightHistory))
        (complementBasis
          (tensorPowerSelectedComplementBitstring accepts attempts observedHistory
            required hrequired ι leftHistory)) *
      (inner Complex
          (outputBasis
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι rightHistory))
          (outputBasis right) *
        inner Complex (outputBasis left)
          (outputBasis
            (tensorPowerSelectedOutputBitstring accepts attempts observedHistory
              required hrequired ι leftHistory)))
  change
    (∑ rightHistory, ∑ leftHistory, entryTerm rightHistory leftHistory) =
      ∑ complement,
        inner Complex (inputBasis (splitEquiv.symm (left, complement)))
          (A (inputBasis (splitEquiv.symm (right, complement))))
  have hReindex :
      (∑ rightHistory, ∑ leftHistory, entryTerm rightHistory leftHistory) =
        ∑ rightPair : Qubit.Bitstring (Fin required × ι) ×
            Qubit.Bitstring
              (tensorPowerSelectedSubsystem accepts attempts observedHistory required
                hrequired ι).ComplementCoordinates,
          ∑ leftPair : Qubit.Bitstring (Fin required × ι) ×
              Qubit.Bitstring
                (tensorPowerSelectedSubsystem accepts attempts observedHistory required
                  hrequired ι).ComplementCoordinates,
            entryTerm (splitEquiv.symm rightPair) (splitEquiv.symm leftPair) := by
    apply Fintype.sum_equiv splitEquiv
    intro rightHistory
    apply Fintype.sum_equiv splitEquiv
    intro leftHistory
    simp
  rw [hReindex]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [entryTerm, splitEquiv,
    tensorPowerSelectedOutputBitstring_equiv_symm,
    tensorPowerSelectedComplementBitstring_equiv_symm]
  simp_rw [complementBasis.inner_eq_ite, outputBasis.inner_eq_ite]
  simp
end QEC.Semantics.FiniteInstrument
