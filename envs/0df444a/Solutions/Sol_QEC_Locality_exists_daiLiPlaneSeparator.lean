-- Prove2me | solution 1 for QEC.Locality.exists_daiLiPlaneSeparator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:32.829847+00:00
-- url     : https://prove2.me/submissions/4fa3fcca-97bb-4b27-8fda-463c8e3ea0c7

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_mem_daiLiLowerTenthCandidates
import Theorems.Thm_QEC_Locality_mem_daiLiUpperTenthCandidates
import Theorems.Thm_QEC_Locality_daiLiTenthCore_has_wide_axis
import Theorems.Thm_QEC_Locality_daiLiSeparatorBandCount_pos
import Theorems.Thm_QEC_Locality_exists_daiLiVerticalLowBand
import Theorems.Thm_QEC_Locality_exists_daiLiHorizontalLowBand
import Theorems.Thm_QEC_Locality_exists_daiLiHorizontalCutsAvoid_of_lt_width
import Theorems.Thm_QEC_Locality_exists_daiLiVerticalCutsAvoid_of_lt_width
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
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
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
omit [Fintype ι] [DecidableEq ι] in
private theorem ten_mul_card_coordinate_lt_cut_le_nine_mul_card
    (region : Finset ι) (coordinate : ι → ℝ) {cut upperTenth : ℝ}
    (hTail : daiLiTenthCount region ≤
      (region.filter fun q => upperTenth ≤ coordinate q).card)
    (hCut : cut < upperTenth) :
    10 * (region.filter fun q => coordinate q < cut).card ≤ 9 * region.card := by
  classical
  let lower := region.filter fun q => coordinate q < cut
  let upper := region.filter fun q => upperTenth ≤ coordinate q
  have hDisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro q hLower hUpper
    have hqLower := (Finset.mem_filter.mp hLower).2
    have hqUpper := (Finset.mem_filter.mp hUpper).2
    linarith
  have hUnionSubset : lower ∪ upper ⊆ region := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (Finset.mem_filter.mp hq).1
    · exact (Finset.mem_filter.mp hq).1
  have hSum : lower.card + upper.card ≤ region.card := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hUnionSubset
  change daiLiTenthCount region ≤ upper.card at hTail
  have hTenth : region.card ≤ 10 * daiLiTenthCount region := by
    unfold daiLiTenthCount
    omega
  change 10 * lower.card ≤ 9 * region.card
  omega
omit [Fintype ι] [DecidableEq ι] in
private theorem ten_mul_card_coordinate_gt_cut_le_nine_mul_card
    (region : Finset ι) (coordinate : ι → ℝ) {lowerTenth cut : ℝ}
    (hTail : daiLiTenthCount region ≤
      (region.filter fun q => coordinate q ≤ lowerTenth).card)
    (hCut : lowerTenth < cut) :
    10 * (region.filter fun q => cut < coordinate q).card ≤ 9 * region.card := by
  classical
  let lower := region.filter fun q => coordinate q ≤ lowerTenth
  let upper := region.filter fun q => cut < coordinate q
  have hDisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro q hLower hUpper
    have hqLower := (Finset.mem_filter.mp hLower).2
    have hqUpper := (Finset.mem_filter.mp hUpper).2
    linarith
  have hUnionSubset : lower ∪ upper ⊆ region := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (Finset.mem_filter.mp hq).1
    · exact (Finset.mem_filter.mp hq).1
  have hSum : lower.card + upper.card ≤ region.card := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_card hUnionSubset
  change daiLiTenthCount region ≤ lower.card at hTail
  have hTenth : region.card ≤ 10 * daiLiTenthCount region := by
    unfold daiLiTenthCount
    omega
  change 10 * upper.card ≤ 9 * region.card
  omega
omit [Fintype ι] [DecidableEq ι] in
private theorem daiLiVerticalSeparatorStrip_subset_equalBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper lowerCut upperCut : ℝ} {m : Nat} {i : Fin m}
    (hLower : daiLiVerticalBandLower lower upper m i < lowerCut)
    (hUpper : upperCut < daiLiVerticalBandUpper lower upper m i) :
    daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ⊆
      daiLiVerticalEqualBand embedding region lower upper m i := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqRegion, hqLower, hqUpper⟩
  apply Finset.mem_filter.mpr
  refine ⟨hqRegion, ?_, ?_⟩
  · exact hLower.le.trans (le_of_lt hqLower)
  · exact hqUpper.trans hUpper
omit [Fintype ι] [DecidableEq ι] in
private theorem daiLiHorizontalSeparatorStrip_subset_equalBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lower upper lowerCut upperCut : ℝ} {m : Nat} {i : Fin m}
    (hLower : daiLiVerticalBandLower lower upper m i < lowerCut)
    (hUpper : upperCut < daiLiVerticalBandUpper lower upper m i) :
    daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ⊆
      daiLiHorizontalEqualBand embedding region lower upper m i := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqRegion, hqLower, hqUpper⟩
  apply Finset.mem_filter.mpr
  refine ⟨hqRegion, ?_, ?_⟩
  · exact hLower.le.trans (le_of_lt hqLower)
  · exact hqUpper.trans hUpper
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
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {ell : ℝ} (hRegion : region.Nonempty) (hTen : 10 ≤ region.card)
    (hEll : 0 < ell) (hScale : ell ≤ Real.sqrt region.card / 8) :
    (∃ lowerCut upperCut : ℝ,
      DaiLiVerticalCutsAvoid embedding region lowerCut upperCut ∧
      ell < upperCut - lowerCut ∧
      ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
        8 * ell * Real.sqrt region.card ∧
      10 * (daiLiVerticalSeparatorLower embedding region lowerCut).card ≤ 9 * region.card ∧
      10 * (daiLiVerticalSeparatorUpper embedding region upperCut).card ≤ 9 * region.card) ∨
    (∃ lowerCut upperCut : ℝ,
      DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut ∧
      ell < upperCut - lowerCut ∧
      ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
        8 * ell * Real.sqrt region.card ∧
      10 * (daiLiHorizontalSeparatorLower embedding region lowerCut).card ≤ 9 * region.card ∧
      10 * (daiLiHorizontalSeparatorUpper embedding region upperCut).card ≤ 9 * region.card) := by
  classical
  let lowerX := daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion
  let upperX := daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion
  let lowerY := daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion
  let upperY := daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion
  have hN : 0 < region.card := Finset.card_pos.mpr hRegion
  have hWide := daiLiTenthCore_has_wide_axis embedding region hRegion hTen
  rcases hWide with hWide | hWide
  · have hWideX : Real.sqrt ((region.card : ℝ) / 10) < upperX - lowerX := by
      simpa [lowerX, upperX, daiLiTenthCoreLower, daiLiTenthCoreUpper] using hWide
    obtain ⟨i, hBandWidth, hBandCard⟩ := exists_daiLiVerticalLowBand embedding region
      hN hEll hScale le_rfl hWideX
    let m := daiLiSeparatorBandCount ell region.card
    obtain ⟨lowerCut, upperCut, hLower, hLowerUpper, hUpperLower, hUpper,
      hCutWidth, hAvoid⟩ :=
      exists_daiLiVerticalCutsAvoid_of_lt_width embedding region hEll.le
        (by simpa [m] using hBandWidth)
    change daiLiVerticalBandLower lowerX upperX m i < lowerCut at hLower
    change lowerCut < daiLiVerticalBandUpper lowerX upperX m i at hLowerUpper
    change daiLiVerticalBandLower lowerX upperX m i < upperCut at hUpperLower
    change upperCut < daiLiVerticalBandUpper lowerX upperX m i at hUpper
    have hM : 0 < m := by
      simpa [m] using daiLiSeparatorBandCount_pos ell region.card
    have hSpan : 0 < upperX - lowerX := by
      exact (Real.sqrt_nonneg ((region.card : ℝ) / 10)).trans_lt hWideX
    have hBandUpperLe : daiLiVerticalBandUpper lowerX upperX m i ≤ upperX := by
      dsimp [daiLiVerticalBandUpper]
      have hIndex : (i : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperX - lowerX) / m := by positivity
      field_simp [ne_of_gt hMReal]
      nlinarith
    have hLowerBandLe : lowerX ≤ daiLiVerticalBandLower lowerX upperX m i := by
      dsimp [daiLiVerticalBandLower]
      have hIndex : 0 ≤ (i : ℝ) := by positivity
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperX - lowerX) / m := by positivity
      nlinarith
    apply Or.inl
    refine ⟨lowerCut, upperCut, hAvoid, hCutWidth, ?_, ?_, ?_⟩
    · have hSubset := daiLiVerticalSeparatorStrip_subset_equalBand embedding region
        (lower := lowerX) (upper := upperX) (i := i) hLower hUpper
      have hSubsetReal : ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
          ((daiLiVerticalEqualBand embedding region lowerX upperX m i).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSubset
      exact hSubsetReal.trans (by simpa [m] using hBandCard)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiUpperTenthCandidates region (fun p => (embedding.point p).1) hRegion)).2
      simpa [daiLiVerticalSeparatorLower, upperX] using
        ten_mul_card_coordinate_lt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).1) hTail (hLowerUpper.trans_le hBandUpperLe)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiLowerTenthCandidates region (fun p => (embedding.point p).1) hRegion)).2
      simpa [daiLiVerticalSeparatorUpper, lowerX] using
        ten_mul_card_coordinate_gt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).1) hTail (lt_of_le_of_lt hLowerBandLe hUpperLower)
  · have hWideY : Real.sqrt ((region.card : ℝ) / 10) < upperY - lowerY := by
      simpa [lowerY, upperY, daiLiTenthCoreLower, daiLiTenthCoreUpper] using hWide
    obtain ⟨i, hBandWidth, hBandCard⟩ := exists_daiLiHorizontalLowBand embedding region
      hN hEll hScale le_rfl hWideY
    let m := daiLiSeparatorBandCount ell region.card
    obtain ⟨lowerCut, upperCut, hLower, hLowerUpper, hUpperLower, hUpper,
      hCutWidth, hAvoid⟩ :=
      exists_daiLiHorizontalCutsAvoid_of_lt_width embedding region hEll.le
        (by simpa [m] using hBandWidth)
    change daiLiVerticalBandLower lowerY upperY m i < lowerCut at hLower
    change lowerCut < daiLiVerticalBandUpper lowerY upperY m i at hLowerUpper
    change daiLiVerticalBandLower lowerY upperY m i < upperCut at hUpperLower
    change upperCut < daiLiVerticalBandUpper lowerY upperY m i at hUpper
    have hM : 0 < m := by
      simpa [m] using daiLiSeparatorBandCount_pos ell region.card
    have hSpan : 0 < upperY - lowerY := by
      exact (Real.sqrt_nonneg ((region.card : ℝ) / 10)).trans_lt hWideY
    have hBandUpperLe : daiLiVerticalBandUpper lowerY upperY m i ≤ upperY := by
      dsimp [daiLiVerticalBandUpper]
      have hIndex : (i : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperY - lowerY) / m := by positivity
      field_simp [ne_of_gt hMReal]
      nlinarith
    have hLowerBandLe : lowerY ≤ daiLiVerticalBandLower lowerY upperY m i := by
      dsimp [daiLiVerticalBandLower]
      have hIndex : 0 ≤ (i : ℝ) := by positivity
      have hMReal : 0 < (m : ℝ) := by exact_mod_cast hM
      have hStep : 0 ≤ (upperY - lowerY) / m := by positivity
      nlinarith
    apply Or.inr
    refine ⟨lowerCut, upperCut, hAvoid, hCutWidth, ?_, ?_, ?_⟩
    · have hSubset := daiLiHorizontalSeparatorStrip_subset_equalBand embedding region
        (lower := lowerY) (upper := upperY) (i := i) hLower hUpper
      have hSubsetReal : ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut).card : ℝ) ≤
          ((daiLiHorizontalEqualBand embedding region lowerY upperY m i).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSubset
      exact hSubsetReal.trans (by simpa [m] using hBandCard)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiUpperTenthCandidates region (fun p => (embedding.point p).2) hRegion)).2
      simpa [daiLiHorizontalSeparatorLower, upperY] using
        ten_mul_card_coordinate_lt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).2) hTail (hLowerUpper.trans_le hBandUpperLe)
    · have hTail := (Finset.mem_filter.mp
        (mem_daiLiLowerTenthCandidates region (fun p => (embedding.point p).2) hRegion)).2
      simpa [daiLiHorizontalSeparatorUpper, lowerY] using
        ten_mul_card_coordinate_gt_cut_le_nine_mul_card region
          (fun p => (embedding.point p).2) hTail (lt_of_le_of_lt hLowerBandLe hUpperLower)
end QEC.Locality
