-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_matrixUnitExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:47.432594+00:00
-- url     : https://prove2.me/submissions/70bff192-51a4-45d9-9e32-c378b8a981ce

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_rankOne_basis
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
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
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)) :
    tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
        required hrequired ι A =
      ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
        ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          (inner Complex
              (tensorPowerBasis
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
                attempts left)
              (A
                (tensorPowerBasis
                  (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
                  attempts right)) *
            inner Complex
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
  let inputBasis :=
    tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
  have hExpand :
      A = ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
        ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          inner Complex (inputBasis left) (A (inputBasis right)) •
            (InnerProductSpace.rankOne Complex
              (inputBasis left) (inputBasis right)).toLinearMap := by
    calc
      A = ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          (InnerProductSpace.rankOne Complex
            (A (inputBasis right)) (inputBasis right)).toLinearMap :=
        QuditSubsystem.operator_eq_sum_rankOne_basis _ inputBasis A
      _ = ∑ right : tensorPowerHistory (Qubit.Bitstring ι) attempts,
          ∑ left : tensorPowerHistory (Qubit.Bitstring ι) attempts,
            inner Complex (inputBasis left) (A (inputBasis right)) •
              (InnerProductSpace.rankOne Complex
                (inputBasis left) (inputBasis right)).toLinearMap := by
        apply Finset.sum_congr rfl
        intro right _
        ext vector
        simp only [LinearMap.sum_apply, LinearMap.smul_apply]
        change
          inner Complex (inputBasis right) vector • A (inputBasis right) =
            ∑ left,
              inner Complex (inputBasis left) (A (inputBasis right)) •
                (inner Complex (inputBasis right) vector • inputBasis left)
        calc
          inner Complex (inputBasis right) vector • A (inputBasis right) =
              inner Complex (inputBasis right) vector •
                ∑ left,
                  inner Complex (inputBasis left) (A (inputBasis right)) •
                    inputBasis left := by
            rw [inputBasis.sum_repr']
          _ = ∑ left,
              inner Complex (inputBasis left) (A (inputBasis right)) •
                (inner Complex (inputBasis right) vector • inputBasis left) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro left _
            simp [smul_smul, mul_comm]
  conv_lhs => rw [hExpand]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro right _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro left _
  rw [map_smul,
    tensorPowerSelectedPartialTraceChannel_rankOne_basis]
  simp only [smul_smul]
  rfl
end QEC.Semantics.FiniteInstrument
