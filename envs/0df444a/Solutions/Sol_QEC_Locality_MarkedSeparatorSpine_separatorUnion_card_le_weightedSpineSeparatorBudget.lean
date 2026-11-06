-- Prove2me | solution 1 for QEC.Locality.MarkedSeparatorSpine.separatorUnion_card_le_weightedSpineSeparatorBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:35:36.414051+00:00
-- url     : https://prove2.me/submissions/4831541f-27df-4925-96b8-7f4f4f949d85

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_markedSpineDecayRatio_lt_one
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
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


attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem separatorUnion_card_le_cardSum (separators : List (Finset ι)) :
    (separators.foldr (· ∪ ·) ∅).card ≤ (separators.map Finset.card).sum := by
  induction separators with
  | nil => simp
  | cons separator separators ih =>
      simpa only [List.foldr_cons, List.map_cons, List.sum_cons] using
        (Finset.card_union_le separator (separators.foldr (· ∪ ·) ∅)).trans
          (Nat.add_le_add_left ih separator.card)
private theorem markedSpineSeparatorUnion_card_le_sum
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    (markedSpineSeparatorUnion spine).card ≤ markedSpineSeparatorCardSum spine := by
  exact separatorUnion_card_le_cardSum spine.separators
private theorem markedSpineDecayRatio_nonneg (exponent : ℝ) :
    0 ≤ markedSpineDecayRatio exponent := by
  exact Real.rpow_nonneg (by norm_num) _
private theorem split_side_rpow_le_markedSpineDecay
    {vertices side : Finset ι} {exponent : ℝ}
    (hbalance : 3 * side.card ≤ 2 * vertices.card) (hexponent : 0 ≤ exponent) :
    Real.rpow side.card exponent ≤
      markedSpineDecayRatio exponent * Real.rpow vertices.card exponent := by
  have hcard : (side.card : ℝ) ≤ (2 / 3 : ℝ) * vertices.card := by
    have hcast : (3 : ℝ) * side.card ≤ 2 * vertices.card := by
      exact_mod_cast hbalance
    linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hcard hexponent
  simpa [markedSpineDecayRatio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (Nat.cast_nonneg vertices.card)] using hpow
private theorem markedSpine_separator_add_childPotential_le
    {vertices child separator : Finset ι} {beta exponent : ℝ}
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    (hseparator : (separator.card : ℝ) ≤ beta * Real.rpow vertices.card exponent)
    (hchild : Real.rpow child.card exponent ≤
      markedSpineDecayRatio exponent * Real.rpow vertices.card exponent) :
    (separator.card : ℝ) + beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow child.card exponent ≤
      beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow vertices.card exponent := by
  have hratio := markedSpineDecayRatio_lt_one hexponent
  have hden : 0 < 1 - markedSpineDecayRatio exponent := sub_pos.mpr hratio
  have hpotential : 0 ≤ beta / (1 - markedSpineDecayRatio exponent) :=
    div_nonneg (zero_le_one.trans hbeta) hden.le
  have hscaled := mul_le_mul_of_nonneg_left hchild hpotential
  have hid : beta + beta / (1 - markedSpineDecayRatio exponent) *
      markedSpineDecayRatio exponent = beta / (1 - markedSpineDecayRatio exponent) := by
    field_simp
    ring
  calc
    (separator.card : ℝ) + beta / (1 - markedSpineDecayRatio exponent) *
          Real.rpow child.card exponent
        ≤ beta * Real.rpow vertices.card exponent +
            beta / (1 - markedSpineDecayRatio exponent) *
              Real.rpow child.card exponent :=
      add_le_add hseparator le_rfl
    _ ≤ beta * Real.rpow vertices.card exponent +
          beta / (1 - markedSpineDecayRatio exponent) *
            (markedSpineDecayRatio exponent * Real.rpow vertices.card exponent) :=
      by simpa only [add_comm] using
        (add_le_add_left hscaled (beta * Real.rpow vertices.card exponent))
    _ = (beta + beta / (1 - markedSpineDecayRatio exponent) *
          markedSpineDecayRatio exponent) * Real.rpow vertices.card exponent := by ring
    _ = beta / (1 - markedSpineDecayRatio exponent) *
          Real.rpow vertices.card exponent := by rw [hid]
private theorem MarkedSeparatorSpine.separatorCardSum_le_profilePotential
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ} (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) :
    (markedSpineSeparatorCardSum spine : ℝ) ≤
      beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow vertices.card exponent := by
  have hbeta : 1 ≤ beta := hProfile.1
  have hexponent : 0 < exponent := hProfile.2.1
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      rename_i vertices left separator right
      simp only [markedSpineSeparatorCardSum, separators, List.map_cons, List.sum_cons,
        List.map_nil, List.sum_nil, Nat.cast_ofNat, Nat.cast_add]
      have hseparator := minimumSeparator_card_real_le_profilePower
        G beta exponent hProfile vertices separator hvertices hminimum
      have hratio := markedSpineDecayRatio_lt_one hexponent
      have hden : 0 < 1 - markedSpineDecayRatio exponent := sub_pos.mpr hratio
      have hcoefficient : beta ≤ beta / (1 - markedSpineDecayRatio exponent) := by
        apply (le_div_iff₀ hden).2
        have hratioNonneg := markedSpineDecayRatio_nonneg exponent
        nlinarith
      simpa using hseparator.trans
        (mul_le_mul_of_nonneg_right hcoefficient
          (Real.rpow_nonneg (Nat.cast_nonneg vertices.card) _))
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      rename_i vertices left separator right
      have hleftPositive : 0 < left.card := by
        have : 0 < (marked ∩ left).card := by omega
        exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
      have hleftCard : 1 ≤ left.card := by omega
      have hseparator := minimumSeparator_card_real_le_profilePower
        G beta exponent hProfile vertices separator hvertices hminimum
      have hchild := split_side_rpow_le_markedSpineDecay hpartition.2.2.2.1 hexponent.le
      have hstep := markedSpine_separator_add_childPotential_le hbeta hexponent hseparator hchild
      simp only [markedSpineSeparatorCardSum, separators, List.map_cons, List.sum_cons,
        Nat.cast_add] at ih ⊢
      linarith [ih hleftCard]
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      rename_i vertices left separator right
      have hrightPositive : 0 < right.card := by
        have : 0 < (marked ∩ right).card := by omega
        exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
      have hrightCard : 1 ≤ right.card := by omega
      have hseparator := minimumSeparator_card_real_le_profilePower
        G beta exponent hProfile vertices separator hvertices hminimum
      have hchild := split_side_rpow_le_markedSpineDecay hpartition.2.2.2.2.1 hexponent.le
      have hstep := markedSpine_separator_add_childPotential_le hbeta hexponent hseparator hchild
      simp only [markedSpineSeparatorCardSum, separators, List.map_cons, List.sum_cons,
        Nat.cast_add] at ih ⊢
      linarith [ih hrightCard]
private theorem MarkedSeparatorSpine.separatorUnion_card_le_profilePotential
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ} (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) :
    ((markedSpineSeparatorUnion spine).card : ℝ) ≤
      beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow vertices.card exponent := by
  exact (Nat.cast_le.2 (markedSpineSeparatorUnion_card_le_sum spine)).trans
    (spine.separatorCardSum_le_profilePotential hProfile hvertices)
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace MarkedSeparatorSpine
theorem _root_.solution
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ}
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) {r : Nat} (hcard : vertices.card ≤ r) :
    (markedSpineSeparatorUnion spine).card ≤
      weightedSpineSeparatorBudget beta exponent r := by
  have hexponent : 0 ≤ exponent := hProfile.2.1.le
  have hpow : Real.rpow vertices.card exponent ≤ Real.rpow r exponent := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hcard) hexponent
  have hcoefficient : 0 ≤ beta / (1 - markedSpineDecayRatio exponent) := by
    exact div_nonneg (zero_le_one.trans hProfile.1)
      (sub_nonneg.mpr (markedSpineDecayRatio_lt_one hProfile.2.1).le)
  have hscaled := mul_le_mul_of_nonneg_left hpow hcoefficient
  have hreal := (spine.separatorUnion_card_le_profilePotential hProfile hvertices).trans hscaled
  exact_mod_cast hreal.trans (Nat.le_ceil _)
end MarkedSeparatorSpine
end QEC.Locality
