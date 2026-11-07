-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.exists_bk_uniform_gap_tradeoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:31:28.102129+00:00
-- url     : https://prove2.me/submissions/3ce4a2b7-48da-4927-918f-7e4adad44b07

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
import Definitions.Def_QEC_Results_LocalityBounds_ConnectivitySeparator
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_eventually_encodedQubits_cast_le_uniform_ceiling
import Theorems.Thm_QEC_Locality_bkEntropyGap_pos
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC.Locality
universe u v
namespace BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
private theorem two_pass_denominator_inv_eq_public_rpow
    {d c : ℝ} (hd : 0 < d) :
    (d ^ (1 - c) * d ^ (1 - c))⁻¹ = d ^ (2 * (c - 1)) := by
  rw [← Real.rpow_add hd]
  rw [show 2 * (c - 1) = -((1 - c) + (1 - c)) by ring, Real.rpow_neg hd.le]
private theorem two_pass_uniform_gap_bound_public_shape
    {k n d c ceiling : ℝ} (hd : 0 < d)
    (hbound : k ≤
      ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * n /
        ((d ^ (1 - c)) * (d ^ (1 - c))) ) :
    k ≤ ((3 / (bkEntropyGap * (1 - ceiling))) *
      (3 / (bkEntropyGap * (1 - ceiling)))) * n * d ^ (2 * (c - 1)) := by
  calc
    k ≤ ((3 / (bkEntropyGap * (1 - ceiling))) *
          (3 / (bkEntropyGap * (1 - ceiling)))) * n /
        ((d ^ (1 - c)) * (d ^ (1 - c))) := hbound
    _ = ((3 / (bkEntropyGap * (1 - ceiling))) *
        (3 / (bkEntropyGap * (1 - ceiling)))) * n * d ^ (2 * (c - 1)) := by
      rw [div_eq_mul_inv, two_pass_denominator_inv_eq_public_rpow hd]
end BKQLDPCFamily
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution
    (family : BKQLDPCFamily iota kappa) (hcofinal : family.HasCofinalValidIndices)
    (huniform : family.UniformCMaxBelowOne) :
    ∃ K : ℝ, 0 < K ∧ family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤ K * i.1 *
        (family.distance i.1 : ℝ) ^ (2 * (family.cMax i - 1))) := by
  rcases hcofinal 0 with ⟨_, _, _⟩
  rcases family.eventually_encodedQubits_cast_le_uniform_ceiling huniform with
    ⟨ceiling, hceiling0, hceiling1, start, hstart⟩
  let K : ℝ := (3 / (bkEntropyGap * (1 - ceiling))) *
    (3 / (bkEntropyGap * (1 - ceiling)))
  have hdenomPos : 0 < bkEntropyGap * (1 - ceiling) :=
    mul_pos bkEntropyGap_pos (sub_pos.mpr hceiling1)
  have hKPos : 0 < K := by
    dsimp [K]
    exact mul_pos (div_pos (by norm_num) hdenomPos) (div_pos (by norm_num) hdenomPos)
  refine ⟨K, hKPos, start, ?_⟩
  intro n hn hvalid
  have hdistance : (0 : ℝ) < family.distance n := by
    exact_mod_cast Nat.zero_lt_two.trans_le (family.distance_two_le n hvalid)
  simpa [K] using two_pass_uniform_gap_bound_public_shape hdistance
    (hstart n hn hvalid)
end QEC.Locality.BKQLDPCFamily
