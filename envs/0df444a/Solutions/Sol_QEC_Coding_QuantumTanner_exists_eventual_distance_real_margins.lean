-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_distance_real_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:13:04.099868+00:00
-- url     : https://prove2.me/submissions/57fec281-5917-4580-ae9b-092803efec1b

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
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
      2 ≤ Delta ∧
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 ∧
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta <
        min (delta / 4) (delta ^ 3 / 12288) * Delta ∧
      (Nat.floor ((Delta : ℝ) ^ gamma) : ℝ) <
        min (min (delta / 4) (delta ^ 3 / 8192)) 1 * Delta ∧
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2) <
        delta ^ 2 / 8 * (Delta : ℝ) ^ (2 : ℝ) ∧
      40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤
        (Nat.floor ((Delta : ℝ) ^ gamma) : ℝ) := by
  obtain ⟨tE, hE⟩ := eventual_power_margin 0 (1 - 2 * epsilon) (1 / 128)
    (by linarith) (by norm_num)
  obtain ⟨tL, hL⟩ := eventual_power_margin ((1 : ℝ) / 2 - epsilon) 1
    (delta * min (delta / 4) (delta ^ 3 / 12288)) (by linarith) (by positivity)
  obtain ⟨tP, hP⟩ := eventual_power_margin gamma 1
    (min (min (delta / 4) (delta ^ 3 / 8192)) 1) hGammaUpper (by positivity)
  obtain ⟨tW, hW⟩ := eventual_power_margin ((3 : ℝ) / 2 - epsilon / 2) 2
    (delta ^ 2 / 8) (by linarith) (by positivity)
  obtain ⟨tB, hB⟩ := eventual_floor_power_lower ((1 : ℝ) / 2 + epsilon) gamma
    (40960 / delta ^ 2) hGammaLower (by linarith) (by positivity)
  refine ⟨max tE (max tL (max tP (max tW tB))), ?_⟩
  intro Delta hDegree
  obtain ⟨hTwo, hExceptional⟩ := hE Delta ((Nat.le_max_left _ _).trans hDegree)
  have hRest := (Nat.le_max_right _ _).trans hDegree
  obtain ⟨_, hLine⟩ := hL Delta ((Nat.le_max_left _ _).trans hRest)
  have hRest' := (Nat.le_max_right _ _).trans hRest
  obtain ⟨_, hPuncture⟩ := hP Delta ((Nat.le_max_left _ _).trans hRest')
  have hRest'' := (Nat.le_max_right _ _).trans hRest'
  obtain ⟨_, hWeight⟩ := hW Delta ((Nat.le_max_left _ _).trans hRest'')
  obtain ⟨_, hLower⟩ := hB Delta ((Nat.le_max_right _ _).trans hRest'')
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hPower : 0 < (Delta : ℝ) ^ (1 - 2 * epsilon) := Real.rpow_pos_of_pos hD _
  have hFraction : 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2 := by
    apply (div_le_iff₀ hPower).mpr
    norm_num only [Real.rpow_zero] at hExceptional
    linarith
  have hLine' : (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / delta <
      min (delta / 4) (delta ^ 3 / 12288) * Delta := by
    apply (div_lt_iff₀ hDeltaDistance).mpr
    simpa only [Real.rpow_one, mul_assoc, mul_left_comm, mul_comm] using hLine
  have hFloor := Nat.floor_le (Real.rpow_nonneg hD.le gamma)
  exact ⟨hTwo, hFraction, hLine', hFloor.trans_lt (by simpa only [Real.rpow_one] using hPuncture),
    hWeight, hLower⟩
end QEC.Coding.QuantumTanner
