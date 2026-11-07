-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_distance_integer_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:17:32.842505+00:00
-- url     : https://prove2.me/submissions/b753f5e4-5960-4da4-ba75-302055650b3d

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Theorems.Thm_QEC_Coding_QuantumTanner_distanceLineError_le_real_bound
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_distance_real_margins
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
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
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
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
namespace QEC.Coding.QuantumTanner
open Filter
private theorem eventual_power_margin
    (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∃ t : Nat, ∀ n : Nat, t ≤ n → 2 ≤ n ∧ (n : ℝ) ^ a < c * (n : ℝ) ^ b := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).eventually (gt_mem_nhds hc)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨t, ht⟩ := eventually_atTop.mp hNat
  refine ⟨max t 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨hTwo, ?_⟩
  calc
    (n : ℝ) ^ a = (n : ℝ) ^ (-(b - a)) * (n : ℝ) ^ b := by
      rw [← Real.rpow_add hPos]
      congr 1
      ring
    _ < c * (n : ℝ) ^ b := mul_lt_mul_of_pos_right
      (ht n ((Nat.le_max_left _ _).trans hn)) (Real.rpow_pos_of_pos hPos _)
private theorem eventual_floor_power_lower
    (a b c : ℝ) (hab : a < b) (hb : 0 < b) (hc : 0 < c) :
    ∃ t : Nat, ∀ n : Nat, t ≤ n →
      2 ≤ n ∧ c * (n : ℝ) ^ a ≤ (Nat.floor ((n : ℝ) ^ b) : ℝ) := by
  obtain ⟨tA, hA⟩ := eventual_power_margin a b (1 / (2 * c)) hab (by positivity)
  obtain ⟨tB, hB⟩ := eventual_power_margin 0 b (1 / 2) hb (by norm_num)
  refine ⟨max tA tB, ?_⟩
  intro n hn
  obtain ⟨hTwo, hSmall⟩ := hA n ((Nat.le_max_left _ _).trans hn)
  obtain ⟨_, hLarge⟩ := hB n ((Nat.le_max_right _ _).trans hn)
  have hFloor := Nat.lt_floor_add_one ((n : ℝ) ^ b)
  have hScaled := mul_lt_mul_of_pos_left hSmall (show 0 < 2 * c by positivity)
  have hCancel : (2 * c) * (1 / (2 * c)) = 1 := by field_simp
  have hScaled' : 2 * c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
    calc
      2 * c * (n : ℝ) ^ a < (2 * c) * ((1 / (2 * c)) * (n : ℝ) ^ b) := hScaled
      _ = (n : ℝ) ^ b := by rw [← mul_assoc, hCancel, one_mul]
  norm_num only [Real.rpow_zero] at hLarge
  exact ⟨hTwo, by linarith⟩
end QEC.Coding.QuantumTanner
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      let d := Nat.ceil (delta * Delta)
      let e := distanceLineError delta epsilon Delta
      let p := Nat.floor ((Delta : ℝ) ^ gamma)
      let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
      2 ≤ Delta ∧ 0 < distanceNormalCutoff epsilon Delta ∧
      distanceNormalCutoff epsilon Delta - 1 ≤ w ∧
      p ≤ Delta ∧ p < d ∧ e < d ∧
      2 * w ≤ (d - p) * (d - p) ∧ 2 * Delta * e ≤ w ∧
      ((6 * Delta * e + 4 * Delta * p : Nat) : ℝ) <
        (d - e : Nat) * (delta ^ 2 * Delta / 256) ∧
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 ∧
      40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤ (p : ℝ) := by
  obtain ⟨tR, hR⟩ := exists_eventual_distance_real_margins delta epsilon gamma
    hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  obtain ⟨tW, hW⟩ := eventual_floor_power_lower ((3 : ℝ) / 2 - epsilon)
    ((3 : ℝ) / 2 - epsilon / 2) (2 / delta) (by linarith) (by linarith) (by positivity)
  refine ⟨max tR tW, ?_⟩
  intro Delta hDegree
  dsimp only
  obtain ⟨hTwo, hFraction, hLine, hPuncture, hWeight, hLower⟩ :=
    hR Delta ((Nat.le_max_left _ _).trans hDegree)
  obtain ⟨_, hErrorWeight⟩ := hW Delta ((Nat.le_max_right _ _).trans hDegree)
  let d := Nat.ceil (delta * Delta)
  let e := distanceLineError delta epsilon Delta
  let p := Nat.floor ((Delta : ℝ) ^ gamma)
  let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hOne : (1 : ℝ) ≤ Delta := by exact_mod_cast (by omega : 1 ≤ Delta)
  have hDistance : delta * Delta ≤ (d : ℝ) := Nat.le_ceil _
  have hError := distanceLineError_le_real_bound delta epsilon Delta (by omega) hDeltaDistance
  have hErrorSmall : (e : ℝ) < min (delta / 4) (delta ^ 3 / 12288) * Delta := hError.trans_lt hLine
  have hErrorDistance : (e : ℝ) < delta / 4 * Delta :=
    hErrorSmall.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hD.le)
  have hErrorCost : (e : ℝ) < delta ^ 3 / 12288 * Delta :=
    hErrorSmall.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le)
  have hPunctureDistance : (p : ℝ) < delta / 4 * Delta := by
    exact hPuncture.trans_le (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_left _ _)) hD.le)
  have hPunctureCost : (p : ℝ) < delta ^ 3 / 8192 * Delta := by
    exact hPuncture.trans_le (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_right _ _)) hD.le)
  have hpDegree : p ≤ Delta := by
    have hReal : (p : ℝ) < Delta :=
      hPuncture.trans_le (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (min_le_right (min (delta / 4) (delta ^ 3 / 8192)) 1) hD.le)
    exact_mod_cast hReal.le
  have hpD : p < d := by exact_mod_cast (by nlinarith : (p : ℝ) < d)
  have heD : e < d := by exact_mod_cast (by nlinarith : (e : ℝ) < d)
  have hCastDP : ((d - p : Nat) : ℝ) = (d : ℝ) - p := by rw [Nat.cast_sub hpD.le]
  have hCastDE : ((d - e : Nat) : ℝ) = (d : ℝ) - e := by rw [Nat.cast_sub heD.le]
  have hDP : 3 * delta * Delta / 4 ≤ ((d - p : Nat) : ℝ) := by rw [hCastDP]; nlinarith
  have hDE : 3 * delta * Delta / 4 ≤ ((d - e : Nat) : ℝ) := by rw [hCastDE]; nlinarith
  have hFloorWeight : (w : ℝ) ≤ (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2) :=
    Nat.floor_le (Real.rpow_nonneg hD.le _)
  have hPunctureBudget : 2 * w ≤ (d - p) * (d - p) := by
    have hDPSquare : (3 * delta * Delta / 4) ^ 2 ≤ (((d - p : Nat) : ℝ)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mpr hDP
    have hWeight' : (2 : ℝ) * w ≤ (((d - p : Nat) : ℝ)) * ((d - p : Nat) : ℝ) := by
      norm_num only [Real.rpow_two] at hWeight
      nlinarith
    exact_mod_cast hWeight'
  have hPowerProduct : (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) =
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
    calc
      (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) =
          (Delta : ℝ) ^ (1 : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) := by rw [Real.rpow_one]
      _ = (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
        rw [← Real.rpow_add hD]
        congr 1
        ring
  have hErrorBudget : 2 * Delta * e ≤ w := by
    have hScaled := mul_le_mul_of_nonneg_left hError (show 0 ≤ 2 * (Delta : ℝ) by positivity)
    have hBound : (2 : ℝ) * Delta * e ≤
        (2 / delta) * (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := by
      calc
        (2 : ℝ) * Delta * e ≤ 2 * Delta * ((Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta) := hScaled
        _ = (2 / delta) * ((Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon)) := by ring
        _ = _ := by rw [hPowerProduct]
    exact_mod_cast hBound.trans hErrorWeight
  have hMargin : ((6 * Delta * e + 4 * Delta * p : Nat) : ℝ) <
      (d - e : Nat) * (delta ^ 2 * Delta / 256) := by
    have hLineScaled := mul_lt_mul_of_pos_left hErrorCost (show 0 < 6 * (Delta : ℝ) by positivity)
    have hPunctureScaled := mul_lt_mul_of_pos_left hPunctureCost (show 0 < 4 * (Delta : ℝ) by positivity)
    have hHeavyScaled := mul_le_mul_of_nonneg_right hDE
      (show 0 ≤ delta ^ 2 * Delta / 256 by positivity)
    have hPositive : 0 < delta ^ 3 * (Delta : ℝ) ^ 2 := by positivity
    push_cast
    nlinarith only [hLineScaled, hPunctureScaled, hHeavyScaled, hPositive]
  have hNormalPos : 0 < distanceNormalCutoff epsilon Delta :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hD _)
  have hNormalWeight : distanceNormalCutoff epsilon Delta - 1 ≤ w := by
    have hCeil := Nat.ceil_lt_add_one (Real.rpow_nonneg hD.le ((3 : ℝ) / 2 - epsilon))
    have hCast : ((distanceNormalCutoff epsilon Delta - 1 : Nat) : ℝ) =
        (distanceNormalCutoff epsilon Delta : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ distanceNormalCutoff epsilon Delta)]
      norm_num
    apply Nat.le_floor
    have hPower := Real.rpow_le_rpow_of_exponent_le hOne
      (show (3 : ℝ) / 2 - epsilon ≤ 3 / 2 - epsilon / 2 by linarith)
    dsimp [distanceNormalCutoff] at hCast ⊢
    linarith only [hCeil, hCast, hPower]
  exact ⟨hTwo, hNormalPos, hNormalWeight, hpDegree, hpD, heD,
    hPunctureBudget, hErrorBudget, hMargin, hFraction, hLower⟩
end QEC.Coding.QuantumTanner
