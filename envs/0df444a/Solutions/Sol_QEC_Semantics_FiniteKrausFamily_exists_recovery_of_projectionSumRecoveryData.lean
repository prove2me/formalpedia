-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.exists_recovery_of_projectionSumRecoveryData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:54.759833+00:00
-- url     : https://prove2.me/submissions/9d49a374-b445-4c1e-bc18-46aeabf8bbea

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (R : κ → KrausOperator H H)
    (S : Operator H)
    (hS_sum : S = ∑ a : κ, (LinearMap.adjoint (R a)).comp (R a))
    (hS_adjoint : LinearMap.adjoint S = S)
    (hS_idempotent : S.comp S = S)
    (hbranches : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ a : κ, (R a).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R a)))) =
          rho.toOperator)
    (hresidual : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (1 - S).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) = 0) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C E recovery := by
  classical
  let recoveryKraus : FiniteKrausFamily (Option κ) H H :=
    { operator := fun a =>
        match a with
        | none => 1 - S
        | some k => R k }
  have hResidualAdjoint : LinearMap.adjoint (1 - S : Operator H) = 1 - S := by
    rw [map_sub, LinearMap.adjoint_one, hS_adjoint]
  have hResidualSquare :
      (LinearMap.adjoint (1 - S : Operator H)).comp (1 - S) = 1 - S := by
    rw [hResidualAdjoint]
    ext x
    have hx := congrArg (fun A : Operator H => A x) hS_idempotent
    simp [LinearMap.comp_apply] at hx ⊢
    rw [hx]
    simp
  have hRecoveryComplete : recoveryKraus.Complete := by
    unfold FiniteKrausFamily.Complete
    dsimp [recoveryKraus]
    rw [Fintype.sum_option]
    rw [hResidualSquare]
    rw [← hS_sum]
    ext x
    simp [sub_eq_add_neg]
  refine ⟨recoveryKraus.toQuantumChannel hRecoveryComplete, hE, ?_⟩
  intro rho hρ
  change recoveryKraus.inducedMap (E.inducedMap rho.toOperator) = rho.toOperator
  rw [FiniteKrausFamily.inducedMap_apply]
  dsimp [recoveryKraus]
  rw [Fintype.sum_option]
  change (1 - S).comp
      ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) +
      (∑ a : κ, (R a).comp
        ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R a)))) =
      rho.toOperator
  rw [hresidual rho hρ]
  rw [hbranches rho hρ]
  simp
end QEC.Semantics.FiniteKrausFamily
