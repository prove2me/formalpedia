-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerRegisterProductDensity_matrixEntry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:38:02.314263+00:00
-- url     : https://prove2.me/submissions/c23a27e0-caee-4b20-9e52-8e1ae5631f65

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerProductInput_matrixEntry_eq_prod
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedComplementBitstring_equiv_symm
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_fst
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedHistoryBitstringEquiv_apply_snd
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedOutputBitstring_equiv_symm
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
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedComplementBitstring_equiv_symm
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_fst
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedHistoryBitstringEquiv_apply_snd
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedOutputBitstring_equiv_symm
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



set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat)
    (left right : Qubit.Bitstring (Fin attempts × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex left)
        ((tensorPowerRegisterProductDensity ι rho rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
            right)) =
      ∏ trial : Fin attempts,
        inner Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
            (fun port => left (trial, port)))
          (rho.toOperator
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
              (fun port => right (trial, port)))) := by
  let leftHistory :=
    (tensorPowerQubitBitstringEquiv ι attempts).symm left
  let rightHistory :=
    (tensorPowerQubitBitstringEquiv ι attempts).symm right
  have hleftHistoryAt (trial : Fin attempts) :
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts leftHistory trial =
        fun port => left (trial, port) := by
    funext port
    exact congrFun
      ((tensorPowerQubitBitstringEquiv ι attempts).apply_symm_apply left)
      (trial, port)
  have hrightHistoryAt (trial : Fin attempts) :
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts rightHistory trial =
        fun port => right (trial, port) := by
    funext port
    exact congrFun
      ((tensorPowerQubitBitstringEquiv ι attempts).apply_symm_apply right)
      (trial, port)
  calc
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex left)
        ((tensorPowerRegisterProductDensity ι rho rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
            right)) =
      inner Complex
        (tensorPowerQubitRegisterTransport ι attempts
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            leftHistory))
        ((tensorPowerQubitRegisterTransport ι attempts).conjOperator
          (tensorPowerProductInput rho rhoUnit attempts).toOperator
          (tensorPowerQubitRegisterTransport ι attempts
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
              rightHistory))) := by
        simp only [tensorPowerRegisterProductDensity,
          UnitaryTransport.conjDensity_toOperator,
          tensorPowerQubitRegisterTransport_apply_basis]
        simp [leftHistory, rightHistory]
    _ = inner Complex
        (tensorPowerBasis
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
          leftHistory)
        ((tensorPowerProductInput rho rhoUnit attempts).toOperator
          (tensorPowerBasis
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) attempts
            rightHistory)) := by
      rw [UnitaryTransport.conjOperator_apply]
      simp only [LinearEquiv.symm_apply_apply]
      exact (tensorPowerQubitRegisterTransport ι attempts).map_inner _ _
    _ = _ := by
      rw [tensorPowerProductInput_matrixEntry_eq_prod]
      apply Finset.prod_congr rfl
      intro trial _
      rw [hleftHistoryAt trial, hrightHistoryAt trial]
end QEC.Semantics.FiniteInstrument
