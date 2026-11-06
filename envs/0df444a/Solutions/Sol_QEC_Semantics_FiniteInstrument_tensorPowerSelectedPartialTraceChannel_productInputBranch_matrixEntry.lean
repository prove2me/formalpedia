-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_productInputBranch_matrixEntry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:37:51.801275+00:00
-- url     : https://prove2.me/submissions/7063213b-e31c-45d9-9618-d82284ae43ae

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystemOperator
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedTrialProduct
import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerUnitDensity_matrixEntry_eq_one
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_matrixEntry_sum_eq_bornWeight
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_tensorPower_productInput
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums
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
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {κ Ω : Type v} [Fintype κ] [Fintype Ω]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory Ω attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          ((I.tensorPower attempts).branchOperator observedHistory
            (tensorPowerProductInput rho rhoUnit attempts).toOperator)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            right)) =
      (∏ slot : Fin required,
        inner Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
            (fun port => left (slot, port)))
          (I.branchOperator
            (tensorPowerHistoryAt Ω attempts observedHistory
              (tensorPowerAcceptedSelector accepts attempts observedHistory
                required hrequired slot))
            rho.toOperator
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
              (fun port => right (slot, port))))) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts observedHistory
          required hrequired,
        (I.bornWeight
          (tensorPowerHistoryAt Ω attempts observedHistory trial.1) rho : Complex) := by
  rw [branchOperator_tensorPower_productInput]
  rw [tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod]
  rw [tensorPowerUnitDensity_matrixEntry_eq_one]
  simp only [one_mul]
  rw [tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums accepts
    attempts observedHistory required hrequired ι
    (fun trial leftBits rightBits =>
      inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex leftBits)
        (I.branchOperator
          (tensorPowerHistoryAt Ω attempts observedHistory trial) rho.toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex rightBits)))
    left right]
  congr 1
  apply Finset.prod_congr rfl
  intro trial _
  exact branchOperator_matrixEntry_sum_eq_bornWeight
    (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) I
    (tensorPowerHistoryAt Ω attempts observedHistory trial.1) rho
end QEC.Semantics.FiniteInstrument
