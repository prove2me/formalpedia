-- Prove2me | solution 1 for QEC.Locality.profileSeparator_child_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:35:35.474473+00:00
-- url     : https://prove2.me/submissions/1d6164c4-ce05-4813-b694-f453bc3bb901

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_minimumSeparator_card_real_le_profilePower
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
namespace QEC.Locality
universe u
private theorem profilePower_le_twelfth_of_threshold
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : exponent < 1)
    {scale : Nat} (hscale : profileSeparatorThreshold beta exponent ≤ scale) :
    12 * beta * Real.rpow scale exponent ≤ (scale : ℝ) := by
  let gap : ℝ := 1 - exponent
  let base : ℝ := 12 * beta
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hbase : 0 < base := by
    dsimp [base]
    nlinarith
  have hscaleNonneg : 0 ≤ (scale : ℝ) := Nat.cast_nonneg scale
  have hthreshold : base ^ gap⁻¹ ≤ (scale : ℝ) := by
    calc
      base ^ gap⁻¹ ≤ (profileSeparatorThreshold beta exponent : ℝ) := by
        simpa [profileSeparatorThreshold, base, gap] using
          (Nat.le_ceil ((12 * beta) ^ ((1 - exponent)⁻¹)))
      _ ≤ (scale : ℝ) := by exact_mod_cast hscale
  have hgapPow : base ≤ (scale : ℝ) ^ gap := by
    calc
      base = (base ^ gap⁻¹) ^ gap := by
        rw [← Real.rpow_mul hbase.le]
        field_simp [hgap.ne']
        simp
      _ ≤ (scale : ℝ) ^ gap :=
        Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hthreshold hgap.le
  have hscalePos : 0 < (scale : ℝ) :=
    (Real.rpow_pos_of_pos hbase _).trans_le hthreshold
  have hfactor : (scale : ℝ) ^ exponent * (scale : ℝ) ^ gap = scale := by
    rw [← Real.rpow_add hscalePos]
    dsimp [gap]
    ring_nf
    exact Real.rpow_one _
  calc
    12 * beta * Real.rpow scale exponent = base * (scale : ℝ) ^ exponent := by
      simp [base]
    _ ≤ (scale : ℝ) ^ gap * (scale : ℝ) ^ exponent := by
      exact mul_le_mul_of_nonneg_right hgapPow (Real.rpow_nonneg hscaleNonneg _)
    _ = (scale : ℝ) := by
      rw [mul_comm]
      exact hfactor
private theorem separatorChild_card_lt_of_balanced_and_twelfth
    {parent child separator : Nat} (hparent : 0 < parent)
    (hbalanced : 3 * child ≤ 2 * parent) (hseparator : 12 * separator ≤ parent) :
    child + separator < parent := by
  omega
private theorem profileSeparator_separator_card_twelfth
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1)
    {vertices separator : Finset ι}
    (hvertices : 1 ≤ vertices.card)
    (hscale : profileSeparatorThreshold beta exponent ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    12 * separator.card ≤ vertices.card := by
  have hprofileReal := minimumSeparator_card_real_le_profilePower
    G beta exponent hProfile vertices separator hvertices hminimum
  have hpower := profilePower_le_twelfth_of_threshold hProfile.1 hexponent hscale
  have hseparatorReal : (12 * separator.card : ℝ) ≤ vertices.card := by
    nlinarith
  exact_mod_cast hseparatorReal
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
namespace QEC.Locality
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1)
    {vertices left separator : Finset ι}
    (hvertices : 1 ≤ vertices.card)
    (hscale : profileSeparatorThreshold beta exponent ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
    (hbalanced : 3 * left.card ≤ 2 * vertices.card) :
    left.card + separator.card < vertices.card := by
  have hseparator := profileSeparator_separator_card_twelfth
    G beta exponent hProfile hexponent hvertices hscale hminimum
  exact separatorChild_card_lt_of_balanced_and_twelfth
    (by omega) hbalanced hseparator
end QEC.Locality
