-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.prepareFactorized_apply_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:49:20.882753+00:00
-- url     : https://prove2.me/submissions/f1fa0646-74c3-47d7-9213-e72f481f28a3

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) (k l : S.complementSystem) :
    S.prepareFactorized rho
        (InnerProductSpace.rankOne Complex k l).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (S.densityEnsembleVectors rho i ⊗ₜ[Complex] k)
        (S.densityEnsembleVectors rho i ⊗ₜ[Complex] l)).toLinearMap := by
  unfold prepareFactorized
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply LinearMap.ext
  intro x
  simp [prepareFactorizedKraus_operator, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply, LinearMap.adjoint_inner_right]
end QEC.Semantics.QuditSubsystem
