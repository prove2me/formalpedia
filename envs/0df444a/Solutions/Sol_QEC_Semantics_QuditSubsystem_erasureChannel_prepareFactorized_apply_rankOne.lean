-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureChannel_prepareFactorized_apply_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:15:52.030393+00:00
-- url     : https://prove2.me/submissions/0c1e0e6e-5237-4cce-9f23-70e7c90bc3f7

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_apply_rankOne
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
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
    S.erasureChannel
      (S.prepareFactorized rho (InnerProductSpace.rankOne Complex k l).toLinearMap) =
      (InnerProductSpace.rankOne Complex k l).toLinearMap := by
  rw [S.prepareFactorized_apply_rankOne rho k l]
  simp only [erasureChannel, QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply, map_sum]
  simp only [conjOperator_rankOne, factorSwap_apply_tmul,
    partialTraceRightRaw_cptp_toLinearMap, partialTraceRightRaw_rankOne_tmul]
  rw [← Finset.sum_smul, S.densityEnsemble_trace_one]
  simp
end QEC.Semantics.QuditSubsystem
