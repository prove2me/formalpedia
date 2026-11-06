-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:11:37.707289+00:00
-- url     : https://prove2.me/submissions/ca1e1509-5b28-4393-b9bb-e655302dee6f

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRejectedCount_succ
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
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


section
universe u v w
namespace QEC
namespace Semantics
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
private theorem tensorPowerBornProduct_sum_eq_one
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (hI : I.kraus.Complete)
    (rho : DensityOperator H) :
    ∀ attempts : Nat,
      ∑ history : tensorPowerHistory Ω attempts,
        tensorPowerBornProduct I rho attempts history = 1
  | 0 => by
      change (∑ _ : PUnit, (1 : ℝ)) = 1
      simp
  | attempts + 1 => by
      change (∑ history : Ω × tensorPowerHistory Ω attempts,
        I.bornWeight history.1 rho * tensorPowerBornProduct I rho attempts history.2) = 1
      rw [Fintype.sum_prod_type]
      calc
        _ = (∑ head : Ω, I.bornWeight head rho) *
            ∑ tail : tensorPowerHistory Ω attempts,
              tensorPowerBornProduct I rho attempts tail := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro head _
          rw [Finset.mul_sum]
        _ = 1 := by
          rw [I.sum_bornWeight_eq_one hI rho,
            tensorPowerBornProduct_sum_eq_one I hI rho attempts]
          norm_num
end FiniteInstrument
end
end Semantics
end QEC
end

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (hI : I.kraus.Complete)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ attempts : Nat,
      tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts =
        (attempts : ℝ) *
          ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
            I.bornWeight outcome rho
  | 0 => by
      simp [tensorPowerRejectedFirstMoment, tensorPowerRejectedCount,
        tensorPowerAcceptedIndices, tensorPowerBornProduct]
  | attempts + 1 => by
      have htotal := tensorPowerBornProduct_sum_eq_one I hI rho attempts
      have hind := solution
        I accepts hI rho rhoUnit attempts
      have hborn :
          (∑ outcome ∈ Finset.univ.filter accepts, I.bornWeight outcome rho) +
            (∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
              I.bornWeight outcome rho) = 1 := by
        calc
          _ = ∑ outcome : Ω, I.bornWeight outcome rho := by
            simpa using Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset Ω)) (p := accepts)
              (f := fun outcome => I.bornWeight outcome rho)
          _ = 1 := I.sum_bornWeight_eq_one hI rho
      change
        (∑ history : Ω × tensorPowerHistory Ω attempts,
          (tensorPowerRejectedCount accepts (attempts + 1) history : ℝ) *
            (I.bornWeight history.1 rho * tensorPowerBornProduct I rho attempts history.2)) =
          ((attempts + 1 : Nat) : ℝ) *
            ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
              I.bornWeight outcome rho
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Ω)) (p := accepts)
        (f := fun head => ∑ tail : tensorPowerHistory Ω attempts,
          (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
            (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail))]
      have haccept (head : Ω) (hhead : accepts head) :
          (∑ tail : tensorPowerHistory Ω attempts,
            (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
              (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            I.bornWeight head rho *
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts := by
        unfold tensorPowerRejectedFirstMoment
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tail _
        rw [tensorPowerRejectedCount_succ]
        simp [hhead]
        ring
      have hreject (head : Ω) (hhead : ¬ accepts head) :
          (∑ tail : tensorPowerHistory Ω attempts,
            (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
              (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            I.bornWeight head rho *
              ((∑ tail : tensorPowerHistory Ω attempts,
                tensorPowerBornProduct I rho attempts tail) +
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts) := by
        unfold tensorPowerRejectedFirstMoment
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro tail _
        rw [tensorPowerRejectedCount_succ]
        simp [hhead]
        ring
      have hsumAccept :
          (∑ head ∈ Finset.univ.filter accepts,
            ∑ tail : tensorPowerHistory Ω attempts,
              (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
                (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            (∑ head ∈ Finset.univ.filter accepts, I.bornWeight head rho) *
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro head hhead
        exact haccept head (Finset.mem_filter.mp hhead).2
      have hsumReject :
          (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
            ∑ tail : tensorPowerHistory Ω attempts,
              (tensorPowerRejectedCount accepts (attempts + 1) (head, tail) : ℝ) *
                (I.bornWeight head rho * tensorPowerBornProduct I rho attempts tail)) =
            (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho) *
              ((∑ tail : tensorPowerHistory Ω attempts,
                tensorPowerBornProduct I rho attempts tail) +
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro head hhead
        exact hreject head (Finset.mem_filter.mp hhead).2
      rw [hsumAccept, hsumReject]
      calc
        _ = ((∑ head ∈ Finset.univ.filter accepts, I.bornWeight head rho) +
              ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
                I.bornWeight head rho) *
              tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts +
            (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho) *
              ∑ tail : tensorPowerHistory Ω attempts,
                tensorPowerBornProduct I rho attempts tail := by
          ring
        _ = tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts +
            ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho := by
          rw [hborn, htotal]
          ring
        _ = (attempts : ℝ) *
              (∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
                I.bornWeight head rho) +
            ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho := by
          rw [hind]
        _ = ((attempts + 1 : Nat) : ℝ) *
            ∑ head ∈ Finset.univ.filter (fun head => ¬ accepts head),
              I.bornWeight head rho := by
          push_cast
          ring
end QEC.Semantics.FiniteInstrument
