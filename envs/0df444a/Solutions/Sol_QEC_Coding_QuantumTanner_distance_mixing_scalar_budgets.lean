-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.distance_mixing_scalar_budgets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:13:49.389502+00:00
-- url     : https://prove2.me/submissions/75caadc6-f4f7-42a5-a096-8cd2656763be

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



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (delta epsilon : ℝ) (Delta s n p : Nat)
    (hDelta : 2 ≤ Delta) (hDeltaDistance : 0 < delta)
    (hSmall : (s : ℝ) ≤ n / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon)))
    (hError : distanceLineError delta epsilon Delta < Nat.ceil (delta * Delta))
    (hDensity : (distanceLineError delta epsilon Delta : ℝ) +
      (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 ≤ delta * Delta / 2)
    (hFractionHalf : 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) ≤ 1 / 2)
    (hPuncture : 40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) ≤ (p : ℝ)) :
    let normal := (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)
    let fraction := 64 / (Delta : ℝ) ^ (1 - 2 * epsilon)
    let gap := delta * Delta / 2
    let ratio := 64 / (delta ^ 2 * Delta)
    let threshold := delta ^ 2 * Delta / 256
    let uniform := 32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)
    2 * ((Delta * Delta : Nat) : ℝ) * s ≤ normal * n ∧
    4 * (4 * (Delta : ℝ)) ^ 2 ≤ fraction * normal ^ 2 ∧
    ((Delta + Delta : Nat) : ℝ) * s + gap * n ≤
      ((Nat.ceil (delta * Delta) - distanceLineError delta epsilon Delta : Nat) : ℝ) * n ∧
    (4 * Real.sqrt (Delta : ℝ)) ^ 2 ≤ ratio * gap ^ 2 ∧
    2 * threshold * ratio ≤ 1 - fraction ∧
    ((Delta + Delta : Nat) : ℝ) * (fraction * s) ≤ uniform * n ∧
    (uniform + 4 * Real.sqrt (Delta : ℝ) *
      Real.sqrt (fraction * (2 * ((Delta + Delta : Nat) : ℝ)))) *
      ((Delta + Delta : Nat) : ℝ) ≤ (p : ℝ) * threshold := by
  dsimp only
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hTwo : (2 : ℝ) ≤ Delta := by exact_mod_cast hDelta
  have hP : 0 < (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := Real.rpow_pos_of_pos hD _
  have hF : 0 < (Delta : ℝ) ^ (1 - 2 * epsilon) := Real.rpow_pos_of_pos hD _
  have hT : 0 < (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) := Real.rpow_pos_of_pos hD _
  have hProduct : (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) *
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) = (Delta : ℝ) ^ 2 := by
    rw [← Real.rpow_add hD]
    norm_num [show (3 : ℝ) / 2 - epsilon + (1 / 2 + epsilon) = 2 by ring]
  have hNormalSquare : ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) ^ 2 =
      (Delta : ℝ) ^ 2 * (Delta : ℝ) ^ (1 - 2 * epsilon) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_natCast _ 2, ← Real.rpow_add hD]
    congr 1
    ring
  have hDensityProduct : (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) *
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) = (Delta : ℝ) := by
    rw [← Real.rpow_add hD, show (1 : ℝ) / 2 - epsilon + (1 / 2 + epsilon) = 1 by ring,
      Real.rpow_one]
  have hMeanProduct : (Delta : ℝ) ^ (1 - 2 * epsilon) *
      ((Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) ^ 2 = (Delta : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_add hD]
    norm_num [show (1 - 2 * epsilon) + ((1 : ℝ) / 2 + epsilon) * 2 = 2 by ring]
  have hRootProduct : (Delta : ℝ) ^ (1 - 2 * epsilon) *
      ((Delta : ℝ) ^ epsilon) ^ 2 = (Delta : ℝ) := by
    rw [← Real.rpow_mul_natCast hD.le, ← Real.rpow_add hD]
    norm_num [show (1 - 2 * epsilon) + epsilon * 2 = 1 by ring]
  have hRoot : Real.sqrt (64 / (Delta : ℝ) ^ (1 - 2 * epsilon) * (4 * Delta)) =
      16 * (Delta : ℝ) ^ epsilon := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    field_simp [hF.ne']
    nlinarith only [hRootProduct]
  have hMixedRoot : Real.sqrt (Delta : ℝ) * (Delta : ℝ) ^ epsilon =
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD]
  have hSmall' := (le_div_iff₀ (show 0 < 4 * (Delta : ℝ) ^ (1 / 2 + epsilon) by positivity)).mp hSmall
  have hSquareSmall : 2 * ((Delta * Delta : Nat) : ℝ) * s ≤
      (Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon) * n := by
    have hScaled := mul_le_mul_of_nonneg_left hSmall' hT.le
    push_cast
    nlinarith only [hScaled, hProduct, (show (0 : ℝ) ≤ s from Nat.cast_nonneg s)]
  have hFraction : 4 * (4 * (Delta : ℝ)) ^ 2 ≤
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon)) ^ 2 := by
    rw [hNormalSquare]
    field_simp
    ring_nf
    norm_num
  have hUnionDensity : ((Delta + Delta : Nat) : ℝ) * s + delta * Delta / 2 * n ≤
      ((Nat.ceil (delta * Delta) - distanceLineError delta epsilon Delta : Nat) : ℝ) * n := by
    have hScaled := mul_le_mul_of_nonneg_left hSmall' (show 0 ≤ (Delta : ℝ) by positivity)
    have hSparse : 2 * (Delta : ℝ) * s ≤
        (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 * n := by
      apply le_of_mul_le_mul_left (a := (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) ?_ hP
      nlinarith only [hScaled, hDensityProduct]
    have hCeil := Nat.le_ceil (delta * (Delta : ℝ))
    have hMargin := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg n)
    have hCeilScaled := mul_le_mul_of_nonneg_right hCeil (Nat.cast_nonneg n)
    rw [Nat.cast_sub hError.le, Nat.cast_add]
    nlinarith only [hSparse, hMargin, hCeilScaled]
  have hRatio : (4 * Real.sqrt (Delta : ℝ)) ^ 2 ≤
      64 / (delta ^ 2 * Delta) * (delta * Delta / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD.le]
    field_simp
    nlinarith
  have hAverage : 2 * (delta ^ 2 * Delta / 256) * (64 / (delta ^ 2 * Delta)) ≤
      1 - 64 / (Delta : ℝ) ^ (1 - 2 * epsilon) := by
    have hCancel : 2 * (delta ^ 2 * Delta / 256) * (64 / (delta ^ 2 * Delta)) = (1 : ℝ) / 2 := by
      field_simp
      ring
    rw [hCancel]
    linarith only [hFractionHalf]
  have hMean : ((Delta + Delta : Nat) : ℝ) * (64 / (Delta : ℝ) ^ (1 - 2 * epsilon) * s) ≤
      (32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) * n := by
    have hScaled := mul_le_mul_of_nonneg_left hSmall' (show 0 ≤ 32 / (Delta : ℝ) *
      (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) by positivity)
    rw [Nat.cast_add]
    apply le_of_mul_le_mul_left (a := (Delta : ℝ) ^ (1 - 2 * epsilon)) ?_ hF
    have hIdentity : (Delta : ℝ) ^ (1 - 2 * epsilon) *
        ((32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) *
          ((s : ℝ) * (4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)))) = 128 * Delta * s := by
      calc
        _ = (128 * s / (Delta : ℝ)) * ((Delta : ℝ) ^ (1 - 2 * epsilon) *
            ((Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) ^ 2) := by ring
        _ = 128 * Delta * s := by
          rw [hMeanProduct]
          field_simp <;> ring
    have hMul := mul_le_mul_of_nonneg_left hScaled hF.le
    rw [hIdentity] at hMul
    convert hMul using 1 <;> field_simp [hF.ne'] <;> ring
  have hSelection : (32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) +
      4 * Real.sqrt (Delta : ℝ) * Real.sqrt (64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        (2 * ((Delta + Delta : Nat) : ℝ)))) * ((Delta + Delta : Nat) : ℝ) ≤
      (p : ℝ) * (delta ^ 2 * Delta / 256) := by
    have hReciprocal : 32 / (Delta : ℝ) ≤ 16 := (div_le_iff₀ hD).mpr (by linarith)
    have hLower := mul_le_mul_of_nonneg_right hPuncture
      (show 0 ≤ delta ^ 2 * (Delta : ℝ) / 256 by positivity)
    have hCancel : (40960 / delta ^ 2 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) *
        (delta ^ 2 * Delta / 256) = 160 * Delta * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
      field_simp
      ring
    rw [hCancel] at hLower
    have hRecScaled := mul_le_mul_of_nonneg_right hReciprocal hP.le
    have hRecScaled' := mul_le_mul_of_nonneg_right hRecScaled (show 0 ≤ 2 * (Delta : ℝ) by positivity)
    simp only [Nat.cast_add]
    rw [show 2 * ((Delta : ℝ) + Delta) = 4 * Delta by ring, hRoot]
    have hMixed : 4 * Real.sqrt (Delta : ℝ) * (16 * (Delta : ℝ) ^ epsilon) =
        64 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
      nlinarith only [hMixedRoot]
    rw [hMixed]
    nlinarith only [hRecScaled', hLower]
  exact ⟨hSquareSmall, hFraction, hUnionDensity, hRatio, hAverage, hMean, hSelection⟩
end QEC.Coding.QuantumTanner
