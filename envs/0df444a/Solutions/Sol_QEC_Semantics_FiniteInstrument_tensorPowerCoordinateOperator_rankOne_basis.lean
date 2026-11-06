-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerCoordinateOperator_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:01:50.995869+00:00
-- url     : https://prove2.me/submissions/39eb6c85-d289-401f-8467-7040783849bd

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
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


attribute [local simp] QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
section
universe u
namespace QEC
namespace Semantics
open scoped TensorProduct
noncomputable section
namespace FiniteInstrument
private theorem tensorPowerBasis_inner_eq_prod
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {beta : Type u} [Fintype beta]
    (basis : OrthonormalBasis beta Complex H) :
    forall (attempts : Nat)
      (left right : tensorPowerHistory beta attempts),
      inner Complex (tensorPowerBasis basis attempts right)
          (tensorPowerBasis basis attempts left) =
        ∏ coordinate : Fin attempts,
          inner Complex
            (basis (tensorPowerHistoryAt beta attempts right coordinate))
            (basis (tensorPowerHistoryAt beta attempts left coordinate)) := by
  intro attempts
  induction attempts with
  | zero =>
      intro left right
      cases left
      cases right
      erw [(tensorPowerBasis basis 0).inner_eq_one]
      simp
  | succ attempts ih =>
      rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩
      rw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply,
        TensorProduct.inner_tmul, Fin.prod_univ_succ]
      simp only [tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ]
      rw [ih leftTail rightTail]
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
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {beta : Type u} [Fintype beta]
    (basis : OrthonormalBasis beta Complex H) :
    forall (attempts : Nat) (trial : Fin attempts)
      (left right : tensorPowerHistory beta attempts),
      tensorPowerCoordinateOperator attempts trial
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis basis attempts left)
            (tensorPowerBasis basis attempts right)).toLinearMap =
        (∏ coordinate : Fin attempts,
            if coordinate = trial then 1
            else inner Complex
              (basis (tensorPowerHistoryAt beta attempts right coordinate))
              (basis (tensorPowerHistoryAt beta attempts left coordinate))) •
          (InnerProductSpace.rankOne Complex
            (basis (tensorPowerHistoryAt beta attempts left trial))
            (basis (tensorPowerHistoryAt beta attempts right trial))).toLinearMap := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro trial
      refine Fin.cases ?_ ?_ trial
      · rintro left right
        rcases left with ⟨leftHead, leftTail⟩
        rcases right with ⟨rightHead, rightTail⟩
        simp only [tensorPowerCoordinateOperator, Fin.cases_zero,
          tensorPowerBasis_succ_apply, partialTraceRightRaw_cptp_toLinearMap]
        erw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
        change partialTraceRightRaw H (tensorPowerCarrier H attempts)
            (InnerProductSpace.rankOne Complex
              (basis leftHead ⊗ₜ[Complex] tensorPowerBasis basis attempts leftTail)
              (basis rightHead ⊗ₜ[Complex] tensorPowerBasis basis attempts rightTail)
            ).toLinearMap = _
        rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
        simp only [Fin.prod_univ_succ, tensorPowerHistoryAt, Fin.cases_zero,
          Fin.cases_succ, if_pos, one_mul, Fin.succ_ne_zero, if_false]
        rw [tensorPowerBasis_inner_eq_prod basis attempts leftTail rightTail]
      · intro tailTrial left right
        rcases left with ⟨leftHead, leftTail⟩
        rcases right with ⟨rightHead, rightTail⟩
        simp only [tensorPowerCoordinateOperator, Fin.cases_succ,
          QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply,
          tensorPowerBasis_succ_apply, partialTraceRightRaw_cptp_toLinearMap]
        erw [tensorPowerBasis_succ_apply, tensorPowerBasis_succ_apply]
        change tensorPowerCoordinateOperator attempts tailTrial
            (partialTraceRightRaw (tensorPowerCarrier H attempts) H
              ((DensityOperator.tensorSwap H (tensorPowerCarrier H attempts)).conjOperator
                (InnerProductSpace.rankOne Complex
                  (basis leftHead ⊗ₜ[Complex] tensorPowerBasis basis attempts leftTail)
                  (basis rightHead ⊗ₜ[Complex] tensorPowerBasis basis attempts rightTail)
                ).toLinearMap)) = _
        rw [QuditSubsystem.conjOperator_rankOne,
          DensityOperator.tensorSwap_apply_tmul,
          DensityOperator.tensorSwap_apply_tmul,
          QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
        rw [map_smul]
        rw [ih tailTrial leftTail rightTail]
        rw [Fin.prod_univ_succ]
        simp only [tensorPowerHistoryAt, Fin.cases_zero, Fin.cases_succ]
        have hzero : (0 : Fin (attempts + 1)) ≠ tailTrial.succ :=
          (Fin.succ_ne_zero tailTrial).symm
        simp only [hzero, if_false, Fin.succ_inj]
        rw [smul_smul]
end QEC.Semantics.FiniteInstrument
