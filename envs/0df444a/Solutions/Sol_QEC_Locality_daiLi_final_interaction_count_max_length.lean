-- Prove2me | solution 1 for QEC.Locality.daiLi_final_interaction_count_max_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:25:39.82658+00:00
-- url     : https://prove2.me/submissions/92ba95a0-32d7-476f-8564-097a3d171db0

import Definitions.Def_QEC_Locality_OptimalTradeoff_CountComposition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
import Theorems.Thm_QEC_Locality_daiLi_final_interaction_count_max_length_of_geometry
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_card_qubitsInRectangle_le_six_mul_area
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_selected_eq
import Theorems.Thm_QEC_Locality_daiLiKGeDFourthRootThreshold_pow_four
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_mem_daiLiGoodExteriorNeighbors_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_one_le_daiLiKGeDFourthRootThreshold
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
private theorem daiLi_encodedQubits_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _
private theorem daiLiFinal_branch_aboveBPT
    {k d n : ℝ} (hn : 0 < n)
    (hAboveBPT : daiLiFinalAboveBPTConstant * n ≤ k * d ^ 2) :
    (100 : ℝ) ^ 4 * n ≤ k * d ^ 2 := by
  rw [daiLiFinalAboveBPTConstant] at hAboveBPT
  nlinarith
private theorem daiLiFinal_distance_ge_seven
    {k d n : ℝ} (hd : 0 < d) (hn : 0 < n) (hKLeN : k ≤ n)
    (hAboveBPT : daiLiFinalAboveBPTConstant * n ≤ k * d ^ 2) :
    (7 : ℝ) ≤ d := by
  have hKDSqLeNDSq : k * d ^ 2 ≤ n * d ^ 2 :=
    mul_le_mul_of_nonneg_right hKLeN (sq_nonneg d)
  have hConstantLeDSq : daiLiFinalAboveBPTConstant ≤ d ^ 2 := by
    by_contra h
    have hSquareSmall : d ^ 2 < daiLiFinalAboveBPTConstant := lt_of_not_ge h
    have hMultSmall : n * d ^ 2 < n * daiLiFinalAboveBPTConstant :=
      mul_lt_mul_of_pos_left hSquareSmall hn
    have hMultLarge : n * daiLiFinalAboveBPTConstant ≤ n * d ^ 2 := by
      calc
        n * daiLiFinalAboveBPTConstant = daiLiFinalAboveBPTConstant * n := by ring
        _ ≤ k * d ^ 2 := hAboveBPT
        _ ≤ n * d ^ 2 := hKDSqLeNDSq
    exact (not_lt_of_ge hMultLarge) hMultSmall
  rw [daiLiFinalAboveBPTConstant] at hConstantLeDSq
  norm_num at hConstantLeDSq
  nlinarith [sq_nonneg (d - 7)]
private theorem daiLiFinal_unit_base_card_lt_distance
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ) (d : ℕ)
    (hDistanceLarge : 7 ≤ d) :
    (centeredRectangleQubits embedding center (1 / 2 : ℝ) (1 / 2 : ℝ)).card < d := by
  have hWidth : (1 : ℝ) ≤ (center.1 + 1 / 2) - (center.1 - 1 / 2) := by norm_num
  have hHeight : (1 : ℝ) ≤ (center.2 + 1 / 2) - (center.2 - 1 / 2) := by norm_num
  have hPacking := embedding.card_qubitsInRectangle_le_six_mul_area
    (center.1 - 1 / 2, center.2 - 1 / 2)
    (center.1 + 1 / 2, center.2 + 1 / 2) hWidth hHeight
  change (embedding.qubitsInRectangle
    (center.1 - 1 / 2, center.2 - 1 / 2)
    (center.1 + 1 / 2, center.2 + 1 / 2)).card < d
  have hCardReal :
      ((embedding.qubitsInRectangle
        (center.1 - 1 / 2, center.2 - 1 / 2)
        (center.1 + 1 / 2, center.2 + 1 / 2)).card : ℝ) ≤ 6 := by
    convert hPacking using 1
    all_goals ring_nf
  have hCard : (embedding.qubitsInRectangle
      (center.1 - 1 / 2, center.2 - 1 / 2)
      (center.1 + 1 / 2, center.2 + 1 / 2)).card ≤ 6 := by
    exact_mod_cast hCardReal
  omega
private theorem daiLiFinal_square_scale_le
    {k d n ell : ℝ} (hk : 0 ≤ k) (hd : 0 < d) (hn : 0 < n) (hKLeN : k ≤ n)
    (hScale : ell = daiLiKGeDFourthRootThreshold k d n) :
    ell ^ 2 ≤ d / 10000 := by
  have hFourth : ell ^ 4 = k * d ^ 2 / (100 ^ 4 * n) := by
    rw [hScale]
    exact daiLiKGeDFourthRootThreshold_pow_four hk hn
  have hFourthBound : ell ^ 4 ≤ d ^ 2 / 100 ^ 4 := by
    rw [hFourth]
    apply (div_le_iff₀ (mul_pos (by positivity : (0 : ℝ) < 100 ^ 4) hn)).2
    have hScaleNonneg : 0 ≤ (n - k) * d ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hKLeN) (sq_nonneg d)
    nlinarith
  by_contra h
  have hSquareLarge : d / 10000 < ell ^ 2 := lt_of_not_ge h
  have hEllSqNonneg : 0 ≤ ell ^ 2 := sq_nonneg ell
  nlinarith [sq_nonneg (ell ^ 2 - d / 10000)]
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
    (hD : 0 < d) (hEncodedPositive : 0 < P.encodedQubits)
    (hAboveBPT : daiLiFinalAboveBPTConstant * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2) :
    max (P.encodedQubits : ℝ) (d : ℝ) / 200 ≤
      (P.longInteractionCount embedding
        (daiLiInteractionCountThreshold (P.encodedQubits : ℝ) d (Fintype.card ι) : ℝ) : ℝ) := by
  have hKLeN : P.encodedQubits ≤ Fintype.card ι := daiLi_encodedQubits_le_blockLength P
  have hNPositiveNat : 0 < Fintype.card ι := lt_of_lt_of_le hEncodedPositive hKLeN
  have hK : 0 ≤ (P.encodedQubits : ℝ) := Nat.cast_nonneg _
  have hDReal : 0 < (d : ℝ) := by exact_mod_cast hD
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hNPositiveNat
  have hKLeNReal : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by exact_mod_cast hKLeN
  have hAboveBPTBranch : (100 : ℝ) ^ 4 * Fintype.card ι ≤
      (P.encodedQubits : ℝ) * (d : ℝ) ^ 2 :=
    daiLiFinal_branch_aboveBPT hN hAboveBPT
  let ell := daiLiKGeDFourthRootThreshold
    (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ)
  let w := daiLiKGeDGridWidth (d : ℝ) ell
  have hScale : ell = daiLiKGeDFourthRootThreshold
      (P.encodedQubits : ℝ) (d : ℝ) (Fintype.card ι : ℝ) := rfl
  have hWidth : w = daiLiKGeDGridWidth (d : ℝ) ell := rfl
  have hEllNat : 1 ≤ ell :=
    one_le_daiLiKGeDFourthRootThreshold hK hN hAboveBPTBranch
  have hEll : 0 < ell := lt_of_lt_of_le (by norm_num) hEllNat
  have hSquareBound : ell ^ 2 ≤ (d : ℝ) / 10000 :=
    daiLiFinal_square_scale_le hK hDReal hN hKLeNReal hScale
  have hWidthProduct : w * ell = (d : ℝ) / 100 := by
    rw [hWidth, daiLiKGeDGridWidth]
    field_simp [hEll.ne']
  have hHundredEllLeWidth : 100 * ell ≤ w := by
    rw [hWidth, daiLiKGeDGridWidth]
    apply (le_div_iff₀ (by nlinarith [hEll])).2
    nlinarith [hSquareBound]
  have hWidthNat : 1 ≤ w := by
    nlinarith [hHundredEllLeWidth, hEllNat]
  have hDistanceLargeReal : (7 : ℝ) ≤ d :=
    daiLiFinal_distance_ge_seven hDReal hN hKLeNReal hAboveBPT
  have hDistanceLarge : 7 ≤ d := by exact_mod_cast hDistanceLargeReal
  let steps : ℕ := Nat.ceil w
  have hStepsBound : w ≤ (steps : ℝ) := by
    dsimp [steps]
    exact_mod_cast (Nat.le_ceil w)
  have hStepsTimesEll : w ≤ (steps : ℝ) * ell := by
    have hProductNonneg : 0 ≤ (steps : ℝ) * (ell - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    nlinarith
  have hBaseHorizontal : (1 / 2 : ℝ) ≤ w / 2 := by
    nlinarith [hWidthNat]
  have hBaseVerticalGood : (1 / 2 : ℝ) ≤ w / 2 := hBaseHorizontal
  have hBaseVerticalBad : (1 / 2 : ℝ) ≤ 5 * ell / 2 := by
    nlinarith [hEllNat]
  have hBaseDiameter : (1 : ℝ) ≤ 2 * (1 / 2 : ℝ) := by norm_num
  have hReach : w / 2 ≤ (1 / 2 : ℝ) + (steps : ℝ) * ell := by
    nlinarith [hStepsTimesEll]
  have hBoundaryBudget :
      48 * (w / 2 + w / 2 + ell) * ell + (d : ℝ) / 10 < d := by
    nlinarith [hWidthProduct, hSquareBound]
  have hShortPackingScale : 60 * w * ell < d := by
    nlinarith [hWidthProduct]
  have hCellWidth : 5 * ell ≤ w := by
    nlinarith [hHundredEllLeWidth]
  have hInternalSideScale : 12 * ell * w < d := by
    nlinarith [hWidthProduct]
  have hGridWidth : 4 * ell ≤ w := by
    nlinarith [hHundredEllLeWidth]
  have hGridLong : 1 ≤ w - 4 * ell := by
    nlinarith [hHundredEllLeWidth, hEllNat]
  have hGridSideSmall : 12 * ell * (w - 4 * ell) < d := by
    nlinarith [hWidthProduct, sq_nonneg ell]
  have hUnitBaseCard (center : ℝ × ℝ) :
      (centeredRectangleQubits embedding center (1 / 2 : ℝ) (1 / 2 : ℝ)).card < d :=
    daiLiFinal_unit_base_card_lt_distance embedding center d hDistanceLarge
  refine daiLi_final_interaction_count_max_length_of_geometry
    P embedding d hDistance ell w hScale hWidth hD hEncodedPositive hAboveBPTBranch hWidthNat
    (1 / 2 : ℝ) (1 / 2 : ℝ) steps hBaseHorizontal hBaseVerticalGood hBaseVerticalBad
    hBaseDiameter hBaseDiameter hReach hReach hReach ?_ ?_ ?_ hBoundaryBudget
    hShortPackingScale hCellWidth hInternalSideScale hGridWidth hGridLong hGridSideSmall
  · intro t atoms rectangles hAtoms hRectangles cell hCandidate
    exact hUnitBaseCard _
  · intro t atoms rectangles hAtoms hRectangles cell slot hCandidate
    exact hUnitBaseCard _
  · intro t cell hOccupied
    exact hUnitBaseCard _
end QEC.Locality
