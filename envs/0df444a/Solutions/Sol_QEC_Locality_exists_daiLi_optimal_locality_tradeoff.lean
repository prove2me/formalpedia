-- Prove2me | solution 1 for QEC.Locality.exists_daiLi_optimal_locality_tradeoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:46:55.749191+00:00
-- url     : https://prove2.me/submissions/defab15c-68c6-4a54-a5d3-96b9bb1e7287

import Definitions.Def_QEC_Locality_OptimalTradeoff_FinalComposition
import Definitions.Def_QEC_Results_LocalityBounds_OptimalTradeoff
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
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_selected_eq
import Theorems.Thm_QEC_Locality_daiLi_final_interaction_count_max_length
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_daiLiBadGridCells_iff
import Theorems.Thm_QEC_Locality_mem_daiLiGoodExteriorNeighbors_iff
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
open Coding.StabilizerCode.StabilizerParameterData
universe u v
private theorem daiLi_distance_le_blockLength
    {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.distance ≤ D.blockLength := by
  rcases D.semanticDistance with ⟨E, _hNotDetectable, hWeight, _hLeast⟩
  rw [← hWeight]
  change (support E).card ≤ Fintype.card ι
  exact Finset.card_le_card (Finset.subset_univ _)
private theorem daiLi_encodedQubits_le_blockLength
    {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.encodedQubits ≤ D.blockLength := by
  rw [D.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _
private theorem daiLi_degenerate_public_conclusion
    {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
    (D : StabilizerParameterData (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι)
    (hAboveBPT : daiLiFinalAboveBPTConstant * (D.blockLength : ℝ) ≤
      (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2)
    (hDistanceLeBlockLength : D.distance ≤ D.blockLength)
    (hEncodedLeBlockLength : D.encodedQubits ≤ D.blockLength)
    (hDegenerate : ¬ 0 < D.distance ∨ ¬ 0 < D.encodedQubits) :
    (1 / 200 : ℝ) * max (D.encodedQubits : ℝ) (D.distance : ℝ) ≤
      (D.presentation.longInteractionCount embedding
        ((1 / 200 : ℝ) * max ((D.distance : ℝ) / Real.sqrt (D.blockLength : ℝ))
          (daiLiFourthRoot
            ((D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 /
              (D.blockLength : ℝ)))) : ℝ) := by
  have hProductZero :
      (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 = 0 := by
    rcases hDegenerate with hDistance | hEncoded
    · have hDistanceZero : D.distance = 0 := Nat.eq_zero_of_not_pos hDistance
      simp [hDistanceZero]
    · have hEncodedZero : D.encodedQubits = 0 := Nat.eq_zero_of_not_pos hEncoded
      simp [hEncodedZero]
  have hConstantPositive : 0 < daiLiFinalAboveBPTConstant := by
    dsimp [daiLiFinalAboveBPTConstant]
    positivity
  have hBlockLengthNonneg : 0 ≤ (D.blockLength : ℝ) := Nat.cast_nonneg _
  have hBlockLengthRealZero : (D.blockLength : ℝ) = 0 := by
    nlinarith [mul_nonneg hConstantPositive.le hBlockLengthNonneg]
  have hBlockLengthZero : D.blockLength = 0 := by
    exact_mod_cast hBlockLengthRealZero
  have hDistanceZero : D.distance = 0 :=
    Nat.eq_zero_of_le_zero (hDistanceLeBlockLength.trans_eq hBlockLengthZero)
  have hEncodedZero : D.encodedQubits = 0 :=
    Nat.eq_zero_of_le_zero (hEncodedLeBlockLength.trans_eq hBlockLengthZero)
  simp [hDistanceZero, hEncodedZero]
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
open Coding.StabilizerCode.StabilizerParameterData
universe u v
namespace QEC.Locality
theorem _root_.solution :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
        (D : StabilizerParameterData (ι := ι) (κ := κ))
        (embedding : UnitSeparatedEmbedding2D ι),
        c1 * (D.blockLength : ℝ) ≤
            (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 →
          c0 * max (D.encodedQubits : ℝ) (D.distance : ℝ) ≤
            (D.presentation.longInteractionCount embedding
              (c0 * max ((D.distance : ℝ) / Real.sqrt (D.blockLength : ℝ))
                (daiLiFourthRoot
                  ((D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 /
                    (D.blockLength : ℝ)))) : ℝ) := by
  refine ⟨1 / 200, daiLiFinalAboveBPTConstant, by norm_num, by
    dsimp [daiLiFinalAboveBPTConstant]
    positivity, ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK D embedding hAboveBPT
  have hDistanceLeBlockLength : D.distance ≤ D.blockLength :=
    daiLi_distance_le_blockLength D
  have hEncodedLeBlockLength : D.encodedQubits ≤ D.blockLength :=
    daiLi_encodedQubits_le_blockLength D
  by_cases hDistancePositive : 0 < D.distance
  · by_cases hEncodedPositive : 0 < D.encodedQubits
    · have hInternal := daiLi_final_interaction_count_max_length D.presentation embedding D.distance
        D.semanticDistance hDistancePositive hEncodedPositive (by
          exact hAboveBPT)
      simpa [daiLiFirstLengthScale, daiLiInteractionCountThreshold,
        StabilizerParameterData.blockLength, StabilizerParameterData.encodedQubits,
        BinaryStabilizerPresentation.blockLength,
        div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInternal
    · exact daiLi_degenerate_public_conclusion D embedding hAboveBPT hDistanceLeBlockLength
        hEncodedLeBlockLength (Or.inr hEncodedPositive)
  · exact daiLi_degenerate_public_conclusion D embedding hAboveBPT hDistanceLeBlockLength
      hEncodedLeBlockLength (Or.inl hDistancePositive)
end QEC.Locality
