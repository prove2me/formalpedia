-- Prove2me | solution 1 for QEC.Locality.daiLi_final_interaction_count_max_length_of_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:08.781256+00:00
-- url     : https://prove2.me/submissions/9c0eaa07-3e05-44da-94fe-8e8417e9b896

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
import Theorems.Thm_QEC_Locality_daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_longInteractionCount_anti_mono
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_selected_eq
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_nonneg
import Theorems.Thm_QEC_Locality_daiLiFourthRoot_pow_four
import Theorems.Thm_QEC_Locality_daiLiKGeD_lowScale_fourthRoot_longInteractionCount
import Theorems.Thm_QEC_Locality_daiLiLargeDistance_interaction_count_lower_bound
import Theorems.Thm_QEC_Locality_exists_daiLiDGeK_two_correctable_partition
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_mem_daiLiGoodExteriorNeighbors_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_one_le_daiLiKGeDFourthRootThreshold
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_two_correctable_regions_encodedQubits_le_separator_card
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
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.daiLiDGeKResidual_selected_eq
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_daiLiBadGridCells_iff
attribute [local simp] QEC.Locality.mem_daiLiGoodExteriorNeighbors_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
private theorem daiLiFirstLengthScale_pow_four (d n : ℝ) (hn : 0 < n) :
    daiLiFirstLengthScale d n ^ 4 = d ^ 4 / n ^ 2 := by
  unfold daiLiFirstLengthScale
  rw [div_pow]
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  calc
    d ^ 4 / Real.sqrt n ^ 4 = d ^ 4 / (Real.sqrt n ^ 2) ^ 2 := by ring
    _ = d ^ 4 / n ^ 2 := by rw [hsq]
private theorem daiLi_firstScale_le_fourthRoot_of_lowScale
    (k d n : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d) (hn : 0 < n)
    (hLowScale : d ≤ Real.sqrt (k * n)) :
    daiLiFirstLengthScale d n ≤ daiLiFourthRoot (k * d ^ 2 / n) := by
  have hKn : 0 ≤ k * n := mul_nonneg hk hn.le
  have hSquare : d ^ 2 ≤ k * n := (Real.le_sqrt hd hKn).mp hLowScale
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  unfold daiLiFirstLengthScale
  apply (pow_le_pow_iff_left₀ (by positivity) (daiLiFourthRoot_nonneg _)
    (by norm_num : 4 ≠ 0)).mp
  rw [daiLiFourthRoot_pow_four _ hRatio,
    show (d / Real.sqrt n) ^ 4 = d ^ 4 / n ^ 2 by
      exact daiLiFirstLengthScale_pow_four d n hn]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  calc
    d ^ 4 = d ^ 2 * d ^ 2 := by ring
    _ ≤ (k * n) * d ^ 2 := mul_le_mul_of_nonneg_right hSquare (sq_nonneg d)
    _ = (k * d ^ 2 / n) * n ^ 2 := by field_simp
private theorem daiLi_fourthRoot_le_firstScale_of_largeDistance
    (k d n : ℝ) (hk : 0 ≤ k) (hd : 0 ≤ d) (hn : 0 < n)
    (hLargeDistance : Real.sqrt (k * n) ≤ d) :
    daiLiFourthRoot (k * d ^ 2 / n) ≤ daiLiFirstLengthScale d n := by
  have hSquare : k * n ≤ d ^ 2 := (Real.sqrt_le_iff).mp hLargeDistance |>.2
  have hRatio : 0 ≤ k * d ^ 2 / n :=
    div_nonneg (mul_nonneg hk (sq_nonneg d)) hn.le
  unfold daiLiFirstLengthScale
  apply (pow_le_pow_iff_left₀ (daiLiFourthRoot_nonneg _) (by positivity)
    (by norm_num : 4 ≠ 0)).mp
  rw [daiLiFourthRoot_pow_four _ hRatio,
    show (d / Real.sqrt n) ^ 4 = d ^ 4 / n ^ 2 by
      exact daiLiFirstLengthScale_pow_four d n hn]
  apply (le_div_iff₀ (sq_pos_of_pos hn)).2
  calc
    (k * d ^ 2 / n) * n ^ 2 = (k * n) * d ^ 2 := by field_simp
    _ ≤ d ^ 2 * d ^ 2 := mul_le_mul_of_nonneg_right hSquare (sq_nonneg d)
    _ = d ^ 4 := by ring
private theorem daiLi_encodedQubits_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _
private theorem daiLiDGeK_lowScale_fourthRoot_longInteractionCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiPrincipalFourthRootScale
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiDGeKGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hDGeK : P.encodedQubits ≤ d)
    (hLowScale : (d : ℝ) ≤ Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι))
    (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * ell)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    (d : ℝ) / 100 < (P.longInteractionCount embedding ell : ℝ) := by
  have hKPositiveNat : 0 < P.encodedQubits := hEncodedPositive
  have hKPositive : 0 < (P.encodedQubits : ℝ) := by exact_mod_cast hKPositiveNat
  have hDReal : 0 < (d : ℝ) := by exact_mod_cast hD
  have hKLeN : P.encodedQubits ≤ Fintype.card ι := daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι := lt_of_lt_of_le hKPositiveNat hKLeN
  have hNPositive : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  by_contra hNotCount
  have hLongCount : (P.longInteractionCount embedding ell : ℝ) ≤ (d : ℝ) / 100 :=
    le_of_not_gt hNotCount
  obtain ⟨t, hResidualLt, _hResidualSubset, hAB, hAC, hBC, hCover,
      ⟨recoveryA, hRecoveryA⟩, ⟨recoveryB, hRecoveryB⟩⟩ :=
    exists_daiLiDGeK_two_correctable_partition P embedding d hDistance ell w ell
      (P.encodedQubits : ℝ) hKPositive hDReal (by exact_mod_cast hDGeK) hNPositive
      hLowScale hScale hWidth hLongCount hGridWidth hEllNat hWidthNat hEllNat le_rfl
      (by nlinarith) hGridLong hGridSideSmall baseHorizontalRadius baseVerticalRadius steps
      hBaseHorizontal hBaseVerticalGood hBaseVerticalBad hBaseHorizontalDiameter
      hBaseVerticalDiameter hReachHorizontal hReachVerticalGood hReachVerticalBad hGoodBaseCard
      hBoundaryBudget hShortPackingScale
  have hDimension := two_correctable_regions_encodedQubits_le_separator_card P
    (daiLiDGeKASubsystem P embedding d ell w ell t)
    (daiLiDGeKTrimmedBSubsystem P embedding d ell w ell t)
    (daiLiDGeKResidualSubsystem P embedding d ell w ell t)
    hAB hAC hBC hCover recoveryA hRecoveryA recoveryB hRecoveryB
  have hDimensionReal : (P.encodedQubits : ℝ) ≤
      ((daiLiDGeKResidualSubsystem P embedding d ell w ell t).selected.card : ℝ) := by
    exact_mod_cast hDimension
  exact (not_lt_of_ge hDimensionReal) hResidualLt
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ)
    (hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ))
    (hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell)
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hAboveBPT : (100 : ℝ) ^ 4 * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2)
    (hWidthNat : 1 ≤ w)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * ell)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * ell)
    (hKGeDGoodBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell,
        Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hKGeDBadBaseCard : ∀ (t : GridTranslation w)
      (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
      (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))),
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell)) →
      (∀ cell ∈ daiLiBadGridCells P embedding ell d w (gridOrigin w t),
        rectangles cell = daiLiPhysicalGreedyRectangles P embedding ell
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
          ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell)) →
      ∀ cell slot,
        Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding ell d w
          (gridOrigin w t) rectangles →
        (centeredRectangleQubits embedding
          (daiLiRectangleCenter
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).1
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles
              (Sum.inr (cell, slot))).2)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hDGeKGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d)
    (hCellWidth : 5 * ell ≤ w) (hInternalSideScale : 12 * ell * w < d)
    (hGridWidth : 4 * ell ≤ w) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    max (P.encodedQubits : ℝ) (d : ℝ) / 200 ≤
      (P.longInteractionCount embedding
        (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι) : ℝ) : ℝ) := by
  have hKLeN : P.encodedQubits ≤ Fintype.card ι := daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι := lt_of_lt_of_le hEncodedPositive hKLeN
  have hK : 0 ≤ (P.encodedQubits : ℝ) := Nat.cast_nonneg _
  have hDReal : 0 < (d : ℝ) := by exact_mod_cast hD
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  have hKLeNReal : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by exact_mod_cast hKLeN
  have hEllNat : 1 ≤ ell := by
    rw [hScale]
    exact one_le_daiLiKGeDFourthRootThreshold hK hN hAboveBPT
  have hPrincipalScale : ell = daiLiPrincipalFourthRootScale
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ) := by
    rw [hScale, daiLiPrincipalFourthRootScale_eq_daiLiKGeDFourthRootThreshold]
    exact hK
    exact hN
  have hDGeKWidth : w = daiLiDGeKGridWidth (d : ℝ) ell := by
    simpa [daiLiKGeDGridWidth, daiLiDGeKGridWidth] using hWidth
  by_cases hLargeDistance :
      Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι) ≤ d
  · have hFourthLeFirst := daiLi_fourthRoot_le_firstScale_of_largeDistance
      (P.encodedQubits : ℝ) d (Fintype.card ι) hK hDReal.le hN hLargeDistance
    have hMaxLength : max (daiLiFirstLengthScale (d : ℝ) (Fintype.card ι))
        (daiLiFourthRoot ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
          Fintype.card ι)) = daiLiFirstLengthScale (d : ℝ) (Fintype.card ι) :=
      max_eq_left hFourthLeFirst
    have hKnLeDSq : (P.encodedQubits : ℝ) * Fintype.card ι ≤ (d : ℝ) ^ 2 :=
      (Real.sqrt_le_iff.mp hLargeDistance).2
    have hKSqLeKN : (P.encodedQubits : ℝ) ^ 2 ≤
        (P.encodedQubits : ℝ) * Fintype.card ι := by
      calc
        (P.encodedQubits : ℝ) ^ 2 = (P.encodedQubits : ℝ) * (P.encodedQubits : ℝ) := by ring
        _ ≤ (P.encodedQubits : ℝ) * Fintype.card ι :=
          mul_le_mul_of_nonneg_left hKLeNReal hK
    have hKLeD : (P.encodedQubits : ℝ) ≤ d := by
      apply (pow_le_pow_iff_left₀ hK hDReal.le (by norm_num : 2 ≠ 0)).mp
      exact hKSqLeKN.trans hKnLeDSq
    have hMaxCount : max (P.encodedQubits : ℝ) (d : ℝ) = d := max_eq_right hKLeD
    have hThreshold : daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d
        (Fintype.card ι) = daiLiLargeDistanceThreshold d (Fintype.card ι) := by
      rw [daiLiInteractionCountThreshold, hMaxLength, daiLiFirstLengthScale,
        daiLiLargeDistanceThreshold]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hN)]
    have hAboveBPTLargeReal : (100 : ℝ) * Fintype.card ι ≤
        (P.encodedQubits : ℝ) * (d : ℝ) ^ 2 := by
      nlinarith [hAboveBPT]
    have hAboveBPTLarge : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2 := by
      exact_mod_cast hAboveBPTLargeReal
    have hCount := daiLiLargeDistance_interaction_count_lower_bound P embedding d hDistance
      hAboveBPTLarge hLargeDistance hEncodedPositive
    have hCountReal : (d : ℝ) ≤ 200 *
        (P.longInteractionCount embedding (daiLiLargeDistanceThreshold d (Fintype.card ι)) : ℝ) := by
      exact_mod_cast hCount
    rw [hMaxCount, hThreshold]
    nlinarith
  · have hLowScale : (d : ℝ) ≤
      Real.sqrt ((P.encodedQubits : ℝ) * Fintype.card ι) :=
      le_of_lt (lt_of_not_ge hLargeDistance)
    have hFirstLeFourth := daiLi_firstScale_le_fourthRoot_of_lowScale
      (P.encodedQubits : ℝ) d (Fintype.card ι) hK hDReal.le hN hLowScale
    have hMaxLength : max (daiLiFirstLengthScale (d : ℝ) (Fintype.card ι))
        (daiLiFourthRoot ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
          Fintype.card ι)) = daiLiFourthRoot ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 /
          Fintype.card ι) := max_eq_right hFirstLeFourth
    have hThresholdLeEll : daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d
        (Fintype.card ι) ≤ ell := by
      rw [daiLiInteractionCountThreshold, hMaxLength, hScale,
        daiLiKGeDFourthRootThreshold]
      have hFourthNonneg := daiLiFourthRoot_nonneg
        ((P.encodedQubits : ℝ) * (d : ℝ) ^ 2 / Fintype.card ι)
      nlinarith
    have hMonoNat := P.longInteractionCount_anti_mono embedding hThresholdLeEll
    have hMono : (P.longInteractionCount embedding ell : ℝ) ≤
        (P.longInteractionCount embedding
          (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι)) : ℝ) := by
      exact_mod_cast hMonoNat
    by_cases hKGeD : d ≤ P.encodedQubits
    · have hCount := daiLiKGeD_lowScale_fourthRoot_longInteractionCount P embedding d
        hDistance ell w hScale hWidth hD hKGeD hLowScale hAboveBPT hWidthNat
        baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
        hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
        hReachVerticalGood hReachVerticalBad hKGeDGoodBaseCard hKGeDBadBaseCard
        hBoundaryBudget hShortPackingScale hCellWidth hInternalSideScale hGridWidth hGridLong
        hGridSideSmall
      have hMaxCount : max (P.encodedQubits : ℝ) (d : ℝ) = P.encodedQubits :=
        max_eq_left (by exact_mod_cast hKGeD)
      rw [hMaxCount]
      nlinarith
    · have hDGeK : P.encodedQubits ≤ d := by omega
      have hCount := daiLiDGeK_lowScale_fourthRoot_longInteractionCount P embedding d
        hDistance ell w hPrincipalScale hDGeKWidth hD hEncodedPositive hDGeK hLowScale
        hWidthNat hEllNat
        baseHorizontalRadius baseVerticalRadius steps hBaseHorizontal hBaseVerticalGood
        hBaseVerticalBad hBaseHorizontalDiameter hBaseVerticalDiameter hReachHorizontal
        hReachVerticalGood hReachVerticalBad hDGeKGoodBaseCard hBoundaryBudget hShortPackingScale
        hGridWidth hGridLong hGridSideSmall
      have hMaxCount : max (P.encodedQubits : ℝ) (d : ℝ) = d :=
        max_eq_right (by exact_mod_cast hDGeK)
      rw [hMaxCount]
      nlinarith
end QEC.Locality
