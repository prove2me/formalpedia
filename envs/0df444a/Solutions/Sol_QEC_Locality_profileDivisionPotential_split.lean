-- Prove2me | solution 1 for QEC.Locality.profileDivisionPotential_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:05.921536+00:00
-- url     : https://prove2.me/submissions/02eddcbf-2da2-47b1-8df7-6b67155f90ae

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Theorems.Thm_QEC_Locality_profileDivisionPotentialCoefficient_nonneg
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
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
private theorem profileDivisionRpowGap_pos
    {exponent : ℝ} (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionRpowGap exponent := by
  have hquarter : (1 / 4 : ℝ) < (1 / 4 : ℝ) ^ exponent :=
    Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hexponent.2
  have hthreeQuarter : (3 / 4 : ℝ) < (3 / 4 : ℝ) ^ exponent :=
    Real.self_lt_rpow_of_lt_one (by norm_num) (by norm_num) hexponent.2
  unfold profileDivisionRpowGap
  linarith
private theorem profileDivisionRpowGap_le_complementary_sum_sub_one
    {exponent t : ℝ} (hexponent : 0 ≤ exponent ∧ exponent ≤ 1)
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    profileDivisionRpowGap exponent ≤ t ^ exponent + (1 - t) ^ exponent - 1 := by
  let a : ℝ := 3 / 2 - 2 * t
  let b : ℝ := 2 * t - 1 / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith [ht.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hba : b + a = 1 := by linarith
  have htCombo : a * (1 / 4 : ℝ) + b * (3 / 4 : ℝ) = t := by
    dsimp [a, b]
    ring
  have hOneSubCombo : b * (1 / 4 : ℝ) + a * (3 / 4 : ℝ) = 1 - t := by
    dsimp [a, b]
    ring
  have hconcave := Real.concaveOn_rpow hexponent.1 hexponent.2
  have htPower := hconcave.2
    (show (1 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (3 / 4 : ℝ) ∈ Set.Ici 0 by norm_num) ha hb hab
  have hOneSubPower := hconcave.2
    (show (1 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (3 / 4 : ℝ) ∈ Set.Ici 0 by norm_num) hb ha hba
  simp only [smul_eq_mul, htCombo] at htPower
  simp only [smul_eq_mul, hOneSubCombo] at hOneSubPower
  have hsum :
      (3 / 4 : ℝ) ^ exponent + (1 / 4 : ℝ) ^ exponent ≤
        t ^ exponent + (1 - t) ^ exponent := by
    calc
      (3 / 4 : ℝ) ^ exponent + (1 / 4 : ℝ) ^ exponent =
          (a * (1 / 4 : ℝ) ^ exponent + b * (3 / 4 : ℝ) ^ exponent) +
            (b * (1 / 4 : ℝ) ^ exponent + a * (3 / 4 : ℝ) ^ exponent) := by
        calc
          _ = 1 * (1 / 4 : ℝ) ^ exponent + 1 * (3 / 4 : ℝ) ^ exponent := by ring
          _ = (a + b) * (1 / 4 : ℝ) ^ exponent +
              (a + b) * (3 / 4 : ℝ) ^ exponent := by rw [hab]
          _ = _ := by ring
      _ ≤ t ^ exponent + (1 - t) ^ exponent := add_le_add htPower hOneSubPower
  unfold profileDivisionRpowGap
  linarith [hsum]
private theorem profileDivisionRpowGap_mul_total_le_children_gap
    {exponent total left right : ℝ} (hexponent : 0 ≤ exponent ∧ exponent ≤ 1)
    (htotal : 0 < total) (hsum : left + right = total)
    (hleftLower : total / 4 ≤ left) (hleftUpper : left ≤ 3 * total / 4) :
    profileDivisionRpowGap exponent * total ^ exponent ≤
      left ^ exponent + right ^ exponent - total ^ exponent := by
  let t := left / total
  have ht : t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
    constructor
    · dsimp [t]
      apply (le_div_iff₀ htotal).2
      nlinarith [hleftLower]
    · dsimp [t]
      apply (div_le_iff₀ htotal).2
      nlinarith [hleftUpper]
  have hunit := profileDivisionRpowGap_le_complementary_sum_sub_one hexponent ht
  have htNonneg : 0 ≤ t := (show (0 : ℝ) ≤ 1 / 4 by norm_num).trans ht.1
  have htLeOne : t ≤ 1 := ht.2.trans (by norm_num)
  have hOneSubNonneg : 0 ≤ 1 - t := sub_nonneg.mpr htLeOne
  have hleft : left = total * t := by
    dsimp [t]
    field_simp [htotal.ne']
  have hright : right = total * (1 - t) := by
    calc
      right = total - left := by linarith [hsum]
      _ = total * (1 - t) := by rw [hleft]; ring
  have hscaled := mul_le_mul_of_nonneg_right hunit
    (Real.rpow_nonneg htotal.le exponent)
  rw [hleft, hright, Real.mul_rpow htotal.le htNonneg,
    Real.mul_rpow htotal.le hOneSubNonneg]
  nlinarith [hscaled]
private theorem profileDivisionPotential_eq_expanded
    {beta exponent : ℝ} {r parent : Nat} (hr : 0 < r) :
    profileDivisionPotential beta exponent r parent =
      profileDivisionPotentialCoefficient beta exponent *
        ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent) -
          (parent : ℝ) ^ exponent) := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hrPowPos : 0 < (r : ℝ) ^ exponent := Real.rpow_pos_of_pos hrReal exponent
  rw [profileDivisionPotential, Real.div_rpow (Nat.cast_nonneg parent) hrReal.le,
    Real.rpow_sub_one hrReal.ne']
  field_simp [hrReal.ne', hrPowPos.ne']
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} {r parent left right separator : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hparent : 0 < parent)
    (hsum : left + right = parent + separator)
    (hleftLower : parent + separator ≤ 4 * left)
    (hleftUpper : 4 * left ≤ 3 * (parent + separator))
    (hseparator : (separator : ℝ) ≤ beta * (parent : ℝ) ^ exponent)
    (hscale :
      profileDivisionPotentialCoefficient beta exponent *
          (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent) ≤ 1) :
    3 * separator + profileDivisionPotential beta exponent r left +
        profileDivisionPotential beta exponent r right ≤
      profileDivisionPotential beta exponent r parent := by
  let coefficient := profileDivisionPotentialCoefficient beta exponent
  let linearScale :=
    (r : ℝ) ^ (exponent - 1) / (1 / 4 : ℝ) ^ (1 - exponent)
  have hsumReal : (left : ℝ) + right = parent + separator := by exact_mod_cast hsum
  have htotalPos : 0 < (parent : ℝ) + separator := by positivity
  have hleftLowerReal : ((parent : ℝ) + separator) / 4 ≤ left := by
    have : (parent : ℝ) + separator ≤ 4 * left := by exact_mod_cast hleftLower
    linarith
  have hleftUpperReal : (left : ℝ) ≤ 3 * ((parent : ℝ) + separator) / 4 := by
    have : (4 : ℝ) * left ≤ 3 * ((parent : ℝ) + separator) := by
      exact_mod_cast hleftUpper
    linarith
  have hconcavity := profileDivisionRpowGap_mul_total_le_children_gap
    (exponent := exponent) (total := (parent : ℝ) + separator)
    (left := left) (right := right) ⟨hexponent.1.le, hexponent.2.le⟩
    htotalPos hsumReal hleftLowerReal hleftUpperReal
  have hparentPower : (parent : ℝ) ^ exponent ≤
      ((parent : ℝ) + separator) ^ exponent := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg parent)
      (le_add_of_nonneg_right (Nat.cast_nonneg separator)) hexponent.1.le
  have hgapNonneg : 0 ≤ profileDivisionRpowGap exponent :=
    (profileDivisionRpowGap_pos hexponent).le
  have hpowerGap :
      profileDivisionRpowGap exponent * (parent : ℝ) ^ exponent ≤
        (left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
          (parent : ℝ) ^ exponent := by
    have hscaledParent := mul_le_mul_of_nonneg_left hparentPower hgapNonneg
    linarith
  have hcoefficientGap :
      coefficient * profileDivisionRpowGap exponent = 4 * beta := by
    dsimp [coefficient, profileDivisionPotentialCoefficient]
    field_simp [(profileDivisionRpowGap_pos hexponent).ne']
  have hseparatorNonneg : (0 : ℝ) ≤ separator := Nat.cast_nonneg separator
  have hscale' : coefficient * linearScale ≤ 1 := by
    calc
      coefficient * linearScale =
          profileDivisionPotentialCoefficient beta exponent *
              (r : ℝ) ^ (exponent - 1) /
                (1 / 4 : ℝ) ^ (1 - exponent) := by
            dsimp [coefficient, linearScale]
            ring
      _ ≤ 1 := hscale
  have hlinearPenalty : coefficient * ((separator : ℝ) * linearScale) ≤ separator := by
    calc
      coefficient * ((separator : ℝ) * linearScale) =
          (separator : ℝ) * (coefficient * linearScale) := by ring
      _ ≤ (separator : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hscale' hseparatorNonneg
      _ = separator := by ring
  have hseparatorPayment : (4 : ℝ) * separator ≤
      coefficient * ((left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
        (parent : ℝ) ^ exponent) := by
    calc
      (4 : ℝ) * separator ≤ 4 * (beta * (parent : ℝ) ^ exponent) := by
        nlinarith [hseparator]
      _ = coefficient *
          (profileDivisionRpowGap exponent * (parent : ℝ) ^ exponent) := by
        calc
          4 * (beta * (parent : ℝ) ^ exponent) =
              (coefficient * profileDivisionRpowGap exponent) *
                (parent : ℝ) ^ exponent := by rw [hcoefficientGap]; ring
          _ = _ := by ring
      _ ≤ coefficient * ((left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
          (parent : ℝ) ^ exponent) := by
        exact mul_le_mul_of_nonneg_left hpowerGap
          (profileDivisionPotentialCoefficient_nonneg hbeta hexponent)
  rw [profileDivisionPotential_eq_expanded hr,
    profileDivisionPotential_eq_expanded hr,
    profileDivisionPotential_eq_expanded hr]
  have hlinearForm (x : ℝ) :
      x * (r : ℝ) ^ (exponent - 1) / (1 / 4 : ℝ) ^ (1 - exponent) =
        x * linearScale := by
    dsimp [linearScale]
    ring
  rw [hlinearForm, hlinearForm, hlinearForm]
  change (3 : ℝ) * separator +
      coefficient * ((left : ℝ) * linearScale - (left : ℝ) ^ exponent) +
      coefficient * ((right : ℝ) * linearScale - (right : ℝ) ^ exponent) ≤
    coefficient * ((parent : ℝ) * linearScale - (parent : ℝ) ^ exponent)
  calc
    (3 : ℝ) * separator +
          coefficient * ((left : ℝ) * linearScale - (left : ℝ) ^ exponent) +
          coefficient * ((right : ℝ) * linearScale - (right : ℝ) ^ exponent) =
        coefficient * ((parent : ℝ) * linearScale - (parent : ℝ) ^ exponent) +
          ((3 : ℝ) * separator + coefficient * ((separator : ℝ) * linearScale) -
            coefficient * ((left : ℝ) ^ exponent + (right : ℝ) ^ exponent -
              (parent : ℝ) ^ exponent)) := by
      have hlinearSum := congrArg
        (fun x : ℝ => coefficient * (x * linearScale)) hsumReal
      linear_combination hlinearSum
    _ ≤ coefficient * ((parent : ℝ) * linearScale - (parent : ℝ) ^ exponent) := by
      nlinarith [hlinearPenalty, hseparatorPayment]
end QEC.Locality
