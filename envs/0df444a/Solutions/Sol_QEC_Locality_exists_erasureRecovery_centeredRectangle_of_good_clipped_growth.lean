-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:18:23.226826+00:00
-- url     : https://prove2.me/submissions/6785ed82-9e51-4f64-a0f9-3fdab06d8e1f

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_regionInteractionCounter_mono
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_centeredRectangleQubits_subset_of_radii_le
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_centeredRectangle_general_growth_iterate
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_eq_target
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
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
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
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


attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ outerHorizontalRadius)
    (hBaseVertical : baseVerticalRadius ≤ outerVerticalRadius)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : outerHorizontalRadius ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : outerVerticalRadius ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding center
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hGoodCounter : 10 * regionInteractionCounter P embedding threshold
      (centeredRectangleQubits embedding center outerHorizontalRadius
        outerVerticalRadius) ≤ d)
    (hBoundaryBudget :
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).erasureChannelFromRegister recovery := by
  let horizontalRadius := centeredRectangleClippedGrowthRadius
    baseHorizontalRadius outerHorizontalRadius threshold
  let verticalRadius := centeredRectangleClippedGrowthRadius
    baseVerticalRadius outerVerticalRadius threshold
  have hHorizontalTarget : horizontalRadius steps = outerHorizontalRadius := by
    simpa [horizontalRadius] using
      centeredRectangleClippedGrowthRadius_eq_target baseHorizontalRadius
        outerHorizontalRadius threshold steps hReachHorizontal
  have hVerticalTarget : verticalRadius steps = outerVerticalRadius := by
    simpa [verticalRadius] using
      centeredRectangleClippedGrowthRadius_eq_target baseVerticalRadius
        outerVerticalRadius threshold steps hReachVertical
  have hGoodCounterReal :
      ((regionInteractionCounter P embedding threshold
        (centeredRectangleQubits embedding center outerHorizontalRadius
          outerVerticalRadius) : Nat) : ℝ) ≤ (d : ℝ) / 10 := by
    have hGoodCounterCast :
        (10 : ℝ) *
          ((regionInteractionCounter P embedding threshold
            (centeredRectangleQubits embedding center outerHorizontalRadius
              outerVerticalRadius) : Nat) : ℝ) ≤ d := by
      exact_mod_cast hGoodCounter
    nlinarith
  rw [← hHorizontalTarget, ← hVerticalTarget]
  apply exists_erasureRecovery_centeredRectangle_general_growth_iterate
    P embedding d hDistance center horizontalRadius verticalRadius threshold steps
    hThreshold
  · intro step hstep
    have hBaseLe : baseHorizontalRadius ≤ horizontalRadius step := by
      dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
      apply le_min hBaseHorizontal
      have hNonneg : 0 ≤ (step : ℝ) * threshold :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      linarith
    nlinarith
  · intro step hstep
    have hBaseLe : baseVerticalRadius ≤ verticalRadius step := by
      dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
      apply le_min hBaseVertical
      have hNonneg : 0 ≤ (step : ℝ) * threshold :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      linarith
    nlinarith
  · intro step hstep
    dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
    apply min_le_min le_rfl
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    nlinarith [hThreshold]
  · intro step hstep
    dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
    apply min_le_min le_rfl
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    nlinarith [hThreshold]
  · intro step hstep
    dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    by_cases hCap : outerHorizontalRadius ≤
        baseHorizontalRadius + (step + 1) * threshold
    · rw [min_eq_left hCap]
      apply le_min
      · linarith
      · have hCap' : outerHorizontalRadius - threshold ≤
            baseHorizontalRadius + step * threshold := by
          norm_num [Nat.cast_add, Nat.cast_one] at hCap ⊢
          nlinarith
        exact hCap'
    · have hNext : baseHorizontalRadius + (step + 1) * threshold ≤
          outerHorizontalRadius := le_of_lt (lt_of_not_ge hCap)
      have hPrevious : baseHorizontalRadius + step * threshold ≤
          outerHorizontalRadius := by
        nlinarith [hThreshold]
      rw [min_eq_right hNext, min_eq_right hPrevious]
      convert le_rfl using 1 <;> first | rfl | ring
  · intro step hstep
    dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
    have hSucc : ((step + 1 : ℕ) : ℝ) = (step : ℝ) + 1 := by norm_num
    rw [hSucc]
    by_cases hCap : outerVerticalRadius ≤
        baseVerticalRadius + (step + 1) * threshold
    · rw [min_eq_left hCap]
      apply le_min
      · linarith
      · have hCap' : outerVerticalRadius - threshold ≤
            baseVerticalRadius + step * threshold := by
          norm_num [Nat.cast_add, Nat.cast_one] at hCap ⊢
          nlinarith
        exact hCap'
    · have hNext : baseVerticalRadius + (step + 1) * threshold ≤
          outerVerticalRadius := le_of_lt (lt_of_not_ge hCap)
      have hPrevious : baseVerticalRadius + step * threshold ≤
          outerVerticalRadius := by
        nlinarith [hThreshold]
      rw [min_eq_right hNext, min_eq_right hPrevious]
      convert le_rfl using 1 <;> first | rfl | ring
  · intro step hstep
    have hHorizontalStep : horizontalRadius step ≤ outerHorizontalRadius := by
      dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hVerticalStep : verticalRadius step ≤ outerVerticalRadius := by
      dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hHorizontalNext : horizontalRadius (step + 1) ≤ outerHorizontalRadius := by
      dsimp [horizontalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hVerticalNext : verticalRadius (step + 1) ≤ outerVerticalRadius := by
      dsimp [verticalRadius, centeredRectangleClippedGrowthRadius]
      exact min_le_left _ _
    have hCounterNat := regionInteractionCounter_mono P embedding threshold
      (centeredRectangleQubits_subset_of_radii_le embedding center
        hHorizontalStep hVerticalStep)
    have hCounterReal :
        ((∑ q ∈ centeredRectangleQubits embedding center
          (horizontalRadius step) (verticalRadius step),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) ≤
        ((regionInteractionCounter P embedding threshold
          (centeredRectangleQubits embedding center outerHorizontalRadius
            outerVerticalRadius) : Nat) : ℝ) := by
      exact_mod_cast hCounterNat
    have hPerimeter :
        48 * (horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold) *
            threshold ≤
          48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold := by
      have hSum : horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold ≤
          outerHorizontalRadius + outerVerticalRadius + threshold := by
        linarith
      have hScaled : 48 *
          (horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold) ≤
          48 * (outerHorizontalRadius + outerVerticalRadius + threshold) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hScaled (by linarith)
    calc
      _ ≤ 48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
          ((regionInteractionCounter P embedding threshold
            (centeredRectangleQubits embedding center outerHorizontalRadius
              outerVerticalRadius) : Nat) : ℝ) := by
        linarith
      _ < _ := by linarith
  · simpa [horizontalRadius, verticalRadius,
      centeredRectangleClippedGrowthRadius,
      hBaseHorizontal, hBaseVertical] using hBaseCard
end QEC.Locality
