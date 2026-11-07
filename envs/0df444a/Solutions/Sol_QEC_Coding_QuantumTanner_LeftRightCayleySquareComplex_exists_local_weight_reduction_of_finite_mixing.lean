-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exists_local_weight_reduction_of_finite_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:23:59.86476+00:00
-- url     : https://prove2.me/submissions/a97056db-1ca7-40e3-ad90-3eccaab5bcce

import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_activeVerticesOnSide_nonempty_of_ne_zero
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptionalVertices_card_bound_of_mixing
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptional_crossCount_le_of_heavy_coverage
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_high_heavy_low_exceptional_vertex
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_local_reduction_of_selected_heavy_vertex
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exists_normal_cover_of_robust
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_normal_card_le_heavy_crossCount_of_covers
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_oppositeHeavySet_card_bound_of_density_gap
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
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w p normalCutoff heavyCutoff : Nat)
    (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hCard : Fintype.card A = Fintype.card B)
    (hDegree : 0 < Fintype.card A + Fintype.card B)
    (hp : p ≤ Fintype.card A) (hpA : p < dA) (hpB : p < dB)
    (hRobust : IsRobust CA CB w)
    (hPunctures : IsRobustWithPunctureResistance CA CB w p)
    (hPunctureBudget : 2 * w ≤ (dA - p) * (dB - p))
    (hNormalCutoff : 0 < normalCutoff) (hWeightBudget : normalCutoff - 1 ≤ w)
    (hRows : (normalCutoff - 1) / dB < dA)
    (hColumns : (normalCutoff - 1) / dA < dB)
    (hHeavyRows : heavyCutoff + (normalCutoff - 1) / dA ≤ dB)
    (hHeavyColumns : heavyCutoff + (normalCutoff - 1) / dB ≤ dA)
    (hErrorBudget : Fintype.card B * ((normalCutoff - 1) / dB) +
      Fintype.card A * ((normalCutoff - 1) / dA) ≤ w)
    (side : Bool) (x : Word (ZMod 2) Square) (hx : x ≠ 0)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (squareSpectral unionSpectral normalThreshold gap fraction ratio uniformBudget threshold : ℝ)
    (hSquareSpectral : 0 ≤ squareSpectral) (hUnionSpectral : 0 ≤ unionSpectral)
    (hNormalThreshold : 0 < normalThreshold) (hNormalRound : normalThreshold ≤ normalCutoff)
    (hGap : 0 < gap) (hFraction : 0 ≤ fraction) (hFractionHalf : fraction ≤ 1 / 2)
    (hThreshold : 0 < threshold)
    (hSquareMixing : HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) squareSpectral)
    (hUnionMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) unionSpectral)
    (hSquareSmall : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤ normalThreshold * Fintype.card G)
    (hFractionBudget : 4 * squareSpectral ^ 2 ≤ fraction * normalThreshold ^ 2)
    (hUnionDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card + gap * Fintype.card G ≤
      (heavyCutoff : ℝ) * Fintype.card G)
    (hRatioBudget : unionSpectral ^ 2 ≤ ratio * gap ^ 2)
    (hAverageBudget : 2 * threshold * ratio ≤ 1 - fraction)
    (hMeanBudget : (Fintype.card A + Fintype.card B : Nat) *
      (fraction * (X.activeVerticesOnSide side x).card) ≤ uniformBudget * Fintype.card G)
    (hSelectionBudget : (uniformBudget + unionSpectral * Real.sqrt
      (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) *
      (Fintype.card A + Fintype.card B : Nat) ≤ (p : ℝ) * threshold)
    (hMargin : (3 * (Fintype.card B * ((normalCutoff - 1) / dB) +
      Fintype.card A * ((normalCutoff - 1) / dA)) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
      (heavyCutoff : ℝ) * threshold) :
    ∃ g : G, ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, !side) x + c) <
        HammingWeight (X.localRestriction (g, !side) x) := by
  let S := X.activeVerticesOnSide side x
  let E := X.exceptionalVerticesOnSide side x normalCutoff
  let N := S \ E
  let T := X.oppositeHeavySet side x heavyCutoff N
  have hES : E ⊆ S := Finset.filter_subset _ _
  have hPartition : N.card + E.card = S.card := by
    simpa only [N, Finset.inter_eq_right.mpr hES] using Finset.card_sdiff_add_card_inter S E
  have hCover := X.exists_normal_cover_of_robust CA CB dA dB w normalCutoff
    hA hB hRobust hNormalCutoff hWeightBudget hRows hColumns side x hLocal
  have hCoverage : N.card ≤ crossCount (X.heavyUnionGraph side x heavyCutoff) N T := by
    apply X.normal_card_le_heavy_crossCount_of_covers side x heavyCutoff N CA CB dA dB
      hA.choose_spec.2.2.2 hB.choose_spec.2.2.2 Finset.sdiff_subset
    intro g hg
    obtain ⟨rows, columns, hMem, hCovered, hRowSmall, hColumnSmall, hRowSize, hColumnSize⟩ :=
      hCover g (Finset.mem_sdiff.mp hg).2
    exact ⟨rows, columns, hMem, hCovered, hRowSmall, hColumnSmall,
      by omega, by omega⟩
  have hExceptional : (E.card : ℝ) ≤ fraction * S.card := by
    have hBound := X.exceptionalVertices_card_bound_of_mixing side x normalCutoff
      normalThreshold squareSpectral hNormalThreshold hNormalRound hSquareSpectral
      hSquareMixing hSquareSmall
    have hScaled := mul_le_mul_of_nonneg_right hFractionBudget (Nat.cast_nonneg S.card)
    apply le_of_mul_le_mul_left (a := normalThreshold ^ 2) ?_ (sq_pos_of_pos hNormalThreshold)
    dsimp [S, E] at *
    nlinarith
  have hHalf : 2 * E.card ≤ S.card := by
    have hScaled := mul_le_mul_of_nonneg_right hFractionHalf (Nat.cast_nonneg S.card)
    exact_mod_cast (by nlinarith : (2 : ℝ) * E.card ≤ S.card)
  have hN : N.Nonempty := by
    have hS : 0 < S.card := Finset.card_pos.mpr (X.activeVerticesOnSide_nonempty_of_ne_zero side x hx)
    apply Finset.card_pos.mp
    omega
  have hTBound : (T.card : ℝ) ≤ ratio * S.card := by
    have hBound := X.oppositeHeavySet_card_bound_of_density_gap hX side x heavyCutoff N
      unionSpectral gap hUnionSpectral hGap hUnionMixing hUnionDensity
    have hScaled := mul_le_mul_of_nonneg_right hRatioBudget (Nat.cast_nonneg S.card)
    apply le_of_mul_le_mul_left (a := gap ^ 2) ?_ (sq_pos_of_pos hGap)
    dsimp [T, S] at *
    nlinarith
  have hAverage : 2 * threshold * T.card ≤ (N.card : ℝ) := by
    have hTScaled := mul_le_mul_of_nonneg_left hTBound (by positivity : 0 ≤ 2 * threshold)
    have hAverageScaled := mul_le_mul_of_nonneg_right hAverageBudget (Nat.cast_nonneg S.card)
    have hPartition' : (N.card : ℝ) + E.card = S.card := by exact_mod_cast hPartition
    nlinarith
  have hBadAverage : (crossCount X.unionCayleyGraph E T : ℝ) ≤
      (uniformBudget + unionSpectral * Real.sqrt
        (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) * T.card := by
    apply X.exceptional_crossCount_le_of_heavy_coverage side x heavyCutoff S E
      unionSpectral fraction uniformBudget hUnionSpectral hFraction hUnionMixing
    · simpa only [Finset.inter_eq_right.mpr hES] using hHalf
    · exact hExceptional
    · exact (mul_le_mul_of_nonneg_left hExceptional
        (Nat.cast_nonneg (Fintype.card A + Fintype.card B))).trans hMeanBudget
    · exact hCoverage
  obtain ⟨g, hg, hHeavy, hBad⟩ := X.exists_high_heavy_low_exceptional_vertex side x
    heavyCutoff N E hN hDegree threshold
    (uniformBudget + unionSpectral * Real.sqrt
      (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) p
    hThreshold (Nat.cast_nonneg p) hCoverage hAverage hBadAverage hSelectionBudget
  refine ⟨g, ?_⟩
  apply X.exists_local_reduction_of_selected_heavy_vertex hX CA CB dA dB w p hA hB
    hCard hp hpA hpB hPunctures hPunctureBudget side x heavyCutoff N E g threshold hHeavy
    (by exact_mod_cast hBad) ((normalCutoff - 1) / dA) ((normalCutoff - 1) / dB)
    hCover hErrorBudget hMargin
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
