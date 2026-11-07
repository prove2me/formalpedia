-- Prove2me | solution 1 for QEC.Locality.daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:43.549081+00:00
-- url     : https://prove2.me/submissions/2e85c681-463a-4ba7-9a01-2b070ed01f3a

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_daiLiLargeDistance_regionIncidence_budget
import Theorems.Thm_QEC_Locality_one_le_daiLiLargeDistanceThreshold_of_positive_encodedQubits
import Theorems.Thm_QEC_Locality_daiLiHorizontalSeparator_cover
import Theorems.Thm_QEC_Locality_daiLiHorizontalSeparatorLower_disjoint_upper
import Theorems.Thm_QEC_Locality_daiLiHorizontalSeparatorSides_separated
import Theorems.Thm_QEC_Locality_daiLiVerticalSeparator_cover
import Theorems.Thm_QEC_Locality_daiLiVerticalSeparatorSides_separated
import Theorems.Thm_QEC_Locality_exists_daiLiPlaneSeparator
import Theorems.Thm_QEC_Locality_daiLiRecursivePotential_step
import Theorems.Thm_QEC_Locality_mem_daiLiGoodExteriorNeighbors_iff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_fixedGeneratorOuterBoundary_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
import Theorems.Thm_QEC_Locality_exists_qudit_erasureRecovery_of_subset
import Theorems.Thm_QEC_Locality_fixedGeneratorDecoupled_of_separated_outside_longEndpoints
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_no_long_interaction_from_outside_endpoint_set
import Theorems.Thm_QEC_Locality_regionInteractionCounter_mono
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
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


attribute [local simp] QEC.Locality.mem_daiLiGoodExteriorNeighbors_iff
section
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
private theorem daiLiGoodExteriorNeighbors_vertical_lower_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiVerticalSeparatorLower embedding region lowerCut) ⊆
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiVerticalSeparatorLower embedding region lowerCut) q).1 hq with
    ⟨hqNotLower, p, hpLower, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiVerticalSeparatorLower embedding region lowerCut ∪
        daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiVerticalSeparatorUpper embedding region upperCut := by
      rw [daiLiVerticalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · exact False.elim (hqNotLower hqLower)
      · exact Finset.mem_union_left _ hqStrip
    · have hSeparated := daiLiVerticalSeparatorSides_separated embedding region hWidth
        hpLower hqUpper
      exact False.elim (not_lt_of_ge hSeparated hpqShort)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpLower).1, hpq, hpqShort⟩
private theorem daiLiGoodExteriorNeighbors_vertical_upper_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiVerticalSeparatorUpper embedding region upperCut) ⊆
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiVerticalSeparatorUpper embedding region upperCut) q).1 hq with
    ⟨hqNotUpper, p, hpUpper, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiVerticalSeparatorLower embedding region lowerCut ∪
        daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiVerticalSeparatorUpper embedding region upperCut := by
      rw [daiLiVerticalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · have hSeparated := daiLiVerticalSeparatorSides_separated embedding region hWidth
            hqLower hpUpper
        exact False.elim (not_lt_of_ge (by
          simpa [UnitSeparatedEmbedding2D.distance_comm] using hSeparated) hpqShort)
      · exact Finset.mem_union_left _ hqStrip
    · exact False.elim (hqNotUpper hqUpper)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpUpper).1, hpq, hpqShort⟩
private theorem daiLiGoodExteriorNeighbors_horizontal_lower_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiHorizontalSeparatorLower embedding region lowerCut) ⊆
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiHorizontalSeparatorLower embedding region lowerCut) q).1 hq with
    ⟨hqNotLower, p, hpLower, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiHorizontalSeparatorLower embedding region lowerCut ∪
        daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiHorizontalSeparatorUpper embedding region upperCut := by
      rw [daiLiHorizontalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · exact False.elim (hqNotLower hqLower)
      · exact Finset.mem_union_left _ hqStrip
    · have hSeparated := daiLiHorizontalSeparatorSides_separated embedding region hWidth
        hpLower hqUpper
      exact False.elim (not_lt_of_ge hSeparated hpqShort)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpLower).1, hpq, hpqShort⟩
private theorem daiLiGoodExteriorNeighbors_horizontal_upper_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut) :
    daiLiGoodExteriorNeighbors P embedding ell
        (daiLiHorizontalSeparatorUpper embedding region upperCut) ⊆
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiGoodExteriorNeighbors P embedding ell region := by
  intro q hq
  rcases (mem_daiLiGoodExteriorNeighbors_iff P embedding ell
    (daiLiHorizontalSeparatorUpper embedding region upperCut) q).1 hq with
    ⟨hqNotUpper, p, hpUpper, hpq, hpqShort⟩
  by_cases hqRegion : q ∈ region
  · have hqPieces : q ∈ daiLiHorizontalSeparatorLower embedding region lowerCut ∪
        daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
          daiLiHorizontalSeparatorUpper embedding region upperCut := by
      rw [daiLiHorizontalSeparator_cover embedding region hAvoid]
      exact hqRegion
    rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
    · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
      · have hSeparated := daiLiHorizontalSeparatorSides_separated embedding region hWidth
            hqLower hpUpper
        exact False.elim (not_lt_of_ge (by
          simpa [UnitSeparatedEmbedding2D.distance_comm] using hSeparated) hpqShort)
      · exact Finset.mem_union_left _ hqStrip
    · exact False.elim (hqNotUpper hqUpper)
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    exact ⟨hqRegion, p, (Finset.mem_filter.mp hpUpper).1, hpq, hpqShort⟩
private theorem card_region_inter_longInteractionEndpoints_le_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) :
    (region ∩ longInteractionEndpointQubits P embedding ell).card ≤
      regionInteractionCounter P embedding ell region := by
  classical
  let endpoints := longInteractionEndpointQubits P embedding ell
  let counter := fun q : ι => P.daiLiInteractionCounter embedding ell q
  calc
    (region ∩ endpoints).card = ∑ q ∈ region ∩ endpoints, 1 := by simp
    _ ≤ ∑ q ∈ region ∩ endpoints, counter q := by
      apply Finset.sum_le_sum
      intro q hq
      have hPositive : 0 < counter q := by
        exact (mem_longInteractionEndpointQubits_iff P embedding ell q).1
          (by simpa [endpoints] using (Finset.mem_inter.mp hq).2)
      omega
    _ ≤ ∑ q ∈ region, counter q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun _ _ _ => Nat.zero_le _)
    _ = regionInteractionCounter P embedding ell region := by
      rfl
omit [Fintype ι] [DecidableEq ι] in
private theorem daiLiVerticalSeparatorLower_disjoint_upper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ} (hCuts : lowerCut ≤ upperCut) :
    Disjoint (daiLiVerticalSeparatorLower embedding region lowerCut)
      (daiLiVerticalSeparatorUpper embedding region upperCut) := by
  apply Finset.disjoint_left.mpr
  intro q hLower hUpper
  have hBelow := (Finset.mem_filter.mp hLower).2
  have hAbove := (Finset.mem_filter.mp hUpper).2
  linarith
private theorem daiLiVertical_unretained_subset_strip_union_endpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut) :
    region \ (daiLiRecursiveGoodPart P embedding ell
        (daiLiVerticalSeparatorLower embedding region lowerCut) ∪
      daiLiRecursiveGoodPart P embedding ell
        (daiLiVerticalSeparatorUpper embedding region upperCut)) ⊆
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell) := by
  intro q hq
  have hqRegion := (Finset.mem_sdiff.mp hq).1
  have hqNotRetained := (Finset.mem_sdiff.mp hq).2
  have hqPieces : q ∈ daiLiVerticalSeparatorLower embedding region lowerCut ∪
      daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiVerticalSeparatorUpper embedding region upperCut := by
    rw [daiLiVerticalSeparator_cover embedding region hAvoid]
    exact hqRegion
  rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
  · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
    · apply Finset.mem_union_right
      apply Finset.mem_inter.mpr
      refine ⟨hqRegion, ?_⟩
      by_contra hqNotEndpoint
      apply hqNotRetained
      apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hqLower, hqNotEndpoint⟩
    · exact Finset.mem_union_left _ hqStrip
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨hqRegion, ?_⟩
    by_contra hqNotEndpoint
    apply hqNotRetained
    apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨hqUpper, hqNotEndpoint⟩
private theorem daiLiHorizontal_unretained_subset_strip_union_endpoints
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut) :
    region \ (daiLiRecursiveGoodPart P embedding ell
        (daiLiHorizontalSeparatorLower embedding region lowerCut) ∪
      daiLiRecursiveGoodPart P embedding ell
        (daiLiHorizontalSeparatorUpper embedding region upperCut)) ⊆
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell) := by
  intro q hq
  have hqRegion := (Finset.mem_sdiff.mp hq).1
  have hqNotRetained := (Finset.mem_sdiff.mp hq).2
  have hqPieces : q ∈ daiLiHorizontalSeparatorLower embedding region lowerCut ∪
      daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        daiLiHorizontalSeparatorUpper embedding region upperCut := by
    rw [daiLiHorizontalSeparator_cover embedding region hAvoid]
    exact hqRegion
  rcases Finset.mem_union.mp hqPieces with hqLeft | hqUpper
  · rcases Finset.mem_union.mp hqLeft with hqLower | hqStrip
    · apply Finset.mem_union_right
      apply Finset.mem_inter.mpr
      refine ⟨hqRegion, ?_⟩
      by_contra hqNotEndpoint
      apply hqNotRetained
      apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨hqLower, hqNotEndpoint⟩
    · exact Finset.mem_union_left _ hqStrip
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨hqRegion, ?_⟩
    by_contra hqNotEndpoint
    apply hqNotRetained
    apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨hqUpper, hqNotEndpoint⟩
private theorem fixedGeneratorOuterBoundary_vertical_goodSides_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut) :
    P.fixedGeneratorOuterBoundary
        ((daiLiRecursiveGoodPart P embedding ell
            (daiLiVerticalSeparatorLower embedding region lowerCut) ∪
          daiLiRecursiveGoodPart P embedding ell
            (daiLiVerticalSeparatorUpper embedding region upperCut) : Finset ι) : Set ι) ⊆
      (((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
          (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region : Finset ι) : Set ι) := by
  let retained : Finset ι := daiLiRecursiveGoodPart P embedding ell
      (daiLiVerticalSeparatorLower embedding region lowerCut) ∪
    daiLiRecursiveGoodPart P embedding ell
      (daiLiVerticalSeparatorUpper embedding region upperCut)
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff (retained : Set ι) q).1 hq with
    ⟨hqNotRetained, p, hpRetained, hpq⟩
  have hpOutside : p ∉ longInteractionEndpointQubits P embedding ell := by
    rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
    · exact (Finset.mem_sdiff.mp hpLower).2
    · exact (Finset.mem_sdiff.mp hpUpper).2
  by_cases hqRegion : q ∈ region
  · apply Finset.mem_union_left
    apply daiLiVertical_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
    refine Finset.mem_sdiff.mpr ⟨hqRegion, ?_⟩
    simpa [retained] using hqNotRetained
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    have hpRegion : p ∈ region := by
      rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpLower).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpUpper).1).1
    have hNotLong : ¬ ell ≤ embedding.distance p q := by
      intro hLong
      apply no_long_interaction_from_outside_endpoint_set P embedding ell p q hpOutside
      change P.fixedGeneratorInteraction p q at hpq
      exact ⟨hpq, hLong⟩
    exact ⟨hqRegion, p, hpRegion, hpq, lt_of_not_ge hNotLong⟩
private theorem fixedGeneratorOuterBoundary_horizontal_goodSides_subset
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι)
    {lowerCut upperCut : ℝ}
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut) :
    P.fixedGeneratorOuterBoundary
        ((daiLiRecursiveGoodPart P embedding ell
            (daiLiHorizontalSeparatorLower embedding region lowerCut) ∪
          daiLiRecursiveGoodPart P embedding ell
            (daiLiHorizontalSeparatorUpper embedding region upperCut) : Finset ι) : Set ι) ⊆
      (((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
          (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region : Finset ι) : Set ι) := by
  let retained : Finset ι := daiLiRecursiveGoodPart P embedding ell
      (daiLiHorizontalSeparatorLower embedding region lowerCut) ∪
    daiLiRecursiveGoodPart P embedding ell
      (daiLiHorizontalSeparatorUpper embedding region upperCut)
  intro q hq
  rcases (P.mem_fixedGeneratorOuterBoundary_iff (retained : Set ι) q).1 hq with
    ⟨hqNotRetained, p, hpRetained, hpq⟩
  have hpOutside : p ∉ longInteractionEndpointQubits P embedding ell := by
    rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
    · exact (Finset.mem_sdiff.mp hpLower).2
    · exact (Finset.mem_sdiff.mp hpUpper).2
  by_cases hqRegion : q ∈ region
  · apply Finset.mem_union_left
    apply daiLiHorizontal_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
    refine Finset.mem_sdiff.mpr ⟨hqRegion, ?_⟩
    simpa [retained] using hqNotRetained
  · apply Finset.mem_union_right
    apply (mem_daiLiGoodExteriorNeighbors_iff P embedding ell region q).2
    have hpRegion : p ∈ region := by
      rcases Finset.mem_union.mp hpRetained with hpLower | hpUpper
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpLower).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpUpper).1).1
    have hNotLong : ¬ ell ≤ embedding.distance p q := by
      intro hLong
      apply no_long_interaction_from_outside_endpoint_set P embedding ell p q hpOutside
      change P.fixedGeneratorInteraction p q at hpq
      exact ⟨hpq, hLong⟩
    exact ⟨hqRegion, p, hpRegion, hpq, lt_of_not_ge hNotLong⟩
private theorem exists_erasureRecovery_daiLiFiniteSubsystem_subset
    (S T : Finset ι) (hST : S ⊆ T)
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (hRecovery : ∃ recovery : QuantumChannel (daiLiFiniteSubsystem T).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem T).complementSystem
        P.semanticCode (daiLiFiniteSubsystem T).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem S).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem S).complementSystem
        P.semanticCode (daiLiFiniteSubsystem S).erasureChannelFromRegister recovery := by
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite (daiLiFiniteSubsystem S))
      (quditSubsystemOfFinite (daiLiFiniteSubsystem T)) hST P.semanticCode hRecovery)
private theorem exists_erasureRecovery_of_daiLiVerticalRecursiveStep
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell : ℝ) (region : Finset ι) {lowerCut upperCut : ℝ}
    (hEll : 0 ≤ ell)
    (hAvoid : DaiLiVerticalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut)
    (hLowerRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiVerticalSeparatorLower embedding region lowerCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorLower embedding region lowerCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorLower embedding region lowerCut)).erasureChannelFromRegister
          recovery)
    (hUpperRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiVerticalSeparatorUpper embedding region upperCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorUpper embedding region upperCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiVerticalSeparatorUpper embedding region upperCut)).erasureChannelFromRegister
          recovery)
    (hBufferSmall :
      ((daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region).card < d) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
        P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery := by
  let lower := daiLiVerticalSeparatorLower embedding region lowerCut
  let upper := daiLiVerticalSeparatorUpper embedding region upperCut
  let goodLower := daiLiRecursiveGoodPart P embedding ell lower
  let goodUpper := daiLiRecursiveGoodPart P embedding ell upper
  let retained := goodLower ∪ goodUpper
  let buffer := (daiLiVerticalSeparatorStrip embedding region lowerCut upperCut ∪
      (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
    daiLiGoodExteriorNeighbors P embedding ell region
  obtain ⟨recoveryGoodLower, hRecoveryGoodLower⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodLower lower
      Finset.sdiff_subset P (by simpa [lower] using hLowerRecovery)
  obtain ⟨recoveryGoodUpper, hRecoveryGoodUpper⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodUpper upper
      Finset.sdiff_subset P (by simpa [upper] using hUpperRecovery)
  have hCutOrder : lowerCut ≤ upperCut := by linarith
  have hGoodDisjoint : Disjoint goodLower goodUpper := by
    apply (daiLiVerticalSeparatorLower_disjoint_upper embedding region
      (lowerCut := lowerCut) (upperCut := upperCut) hCutOrder).mono
    · exact Finset.sdiff_subset
    · exact Finset.sdiff_subset
  have hGoodDecoupled : P.fixedGeneratorDecoupled (goodLower : Set ι) (goodUpper : Set ι) := by
    apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding ell
      goodLower goodUpper hGoodDisjoint
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro p hp q hq
      apply daiLiVerticalSeparatorSides_separated embedding region
        (lowerCut := lowerCut) (upperCut := upperCut) hWidth
      · exact Finset.sdiff_subset hp
      · exact Finset.sdiff_subset hq
  obtain ⟨recoveryRetained, hRecoveryRetained⟩ :=
    exists_erasureRecovery_of_fixedGeneratorDecoupled P
      (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
      recoveryGoodLower recoveryGoodUpper hRecoveryGoodLower hRecoveryGoodUpper
      (by simpa [daiLiFiniteSubsystem] using hGoodDecoupled)
  obtain ⟨recoveryBuffer, hRecoveryBuffer⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      (daiLiFiniteSubsystem buffer) hBufferSmall
  let retainedSubsystem := unionSubsystem
    (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
  let bufferSubsystem := daiLiFiniteSubsystem buffer
  have hBoundary : P.fixedGeneratorOuterBoundary
      (retainedSubsystem.selected : Set ι) ⊆ (bufferSubsystem.selected : Set ι) := by
    change P.fixedGeneratorOuterBoundary (retained : Set ι) ⊆ (buffer : Set ι)
    simpa [retained, buffer, Set.union_assoc] using
      (fixedGeneratorOuterBoundary_vertical_goodSides_subset P embedding ell region hAvoid)
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset P
      retainedSubsystem bufferSubsystem recoveryRetained recoveryBuffer
      (by simpa [retainedSubsystem] using hRecoveryRetained)
      hRecoveryBuffer hBoundary
  have hParentSubset : region ⊆ (unionSubsystem retainedSubsystem bufferSubsystem).selected := by
    change region ⊆ retained ∪ buffer
    intro q hq
    by_cases hqRetained : q ∈ retained
    · apply Finset.mem_union_left
      simpa [retainedSubsystem, retained, daiLiFiniteSubsystem] using hqRetained
    · apply Finset.mem_union_right
      have hqBuffer : q ∈ buffer := by
        apply Finset.mem_union_left
        apply daiLiVertical_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
        exact Finset.mem_sdiff.mpr ⟨hq, hqRetained⟩
      exact hqBuffer
  exact exists_erasureRecovery_daiLiFiniteSubsystem_subset region
    (unionSubsystem retainedSubsystem bufferSubsystem).selected hParentSubset P
    ⟨recoveryExpanded, hRecoveryExpanded⟩
private theorem exists_erasureRecovery_of_daiLiHorizontalRecursiveStep
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell : ℝ) (region : Finset ι) {lowerCut upperCut : ℝ}
    (hEll : 0 ≤ ell)
    (hAvoid : DaiLiHorizontalCutsAvoid embedding region lowerCut upperCut)
    (hWidth : ell ≤ upperCut - lowerCut)
    (hLowerRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiHorizontalSeparatorLower embedding region lowerCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorLower embedding region lowerCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorLower embedding region lowerCut)).erasureChannelFromRegister
          recovery)
    (hUpperRecovery : ∃ recovery : QuantumChannel
      (daiLiFiniteSubsystem (daiLiHorizontalSeparatorUpper embedding region upperCut)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorUpper embedding region upperCut)).complementSystem
        P.semanticCode
        (daiLiFiniteSubsystem (daiLiHorizontalSeparatorUpper embedding region upperCut)).erasureChannelFromRegister
          recovery)
    (hBufferSmall :
      ((daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
        (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
        daiLiGoodExteriorNeighbors P embedding ell region).card < d) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
        P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery := by
  let lower := daiLiHorizontalSeparatorLower embedding region lowerCut
  let upper := daiLiHorizontalSeparatorUpper embedding region upperCut
  let goodLower := daiLiRecursiveGoodPart P embedding ell lower
  let goodUpper := daiLiRecursiveGoodPart P embedding ell upper
  let retained := goodLower ∪ goodUpper
  let buffer := (daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut ∪
      (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
    daiLiGoodExteriorNeighbors P embedding ell region
  obtain ⟨recoveryGoodLower, hRecoveryGoodLower⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodLower lower
      Finset.sdiff_subset P (by simpa [lower] using hLowerRecovery)
  obtain ⟨recoveryGoodUpper, hRecoveryGoodUpper⟩ :=
    exists_erasureRecovery_daiLiFiniteSubsystem_subset goodUpper upper
      Finset.sdiff_subset P (by simpa [upper] using hUpperRecovery)
  have hCutOrder : lowerCut ≤ upperCut := by linarith
  have hGoodDisjoint : Disjoint goodLower goodUpper := by
    apply (daiLiHorizontalSeparatorLower_disjoint_upper embedding region hCutOrder).mono
    · exact Finset.sdiff_subset
    · exact Finset.sdiff_subset
  have hGoodDecoupled : P.fixedGeneratorDecoupled (goodLower : Set ι) (goodUpper : Set ι) := by
    apply fixedGeneratorDecoupled_of_separated_outside_longEndpoints P embedding ell
      goodLower goodUpper hGoodDisjoint
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro q hq
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hq).2
    · intro p hp q hq
      apply daiLiHorizontalSeparatorSides_separated embedding region
        (lowerCut := lowerCut) (upperCut := upperCut) hWidth
      · exact Finset.sdiff_subset hp
      · exact Finset.sdiff_subset hq
  obtain ⟨recoveryRetained, hRecoveryRetained⟩ :=
    exists_erasureRecovery_of_fixedGeneratorDecoupled P
      (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
      recoveryGoodLower recoveryGoodUpper hRecoveryGoodLower hRecoveryGoodUpper
      (by simpa [daiLiFiniteSubsystem] using hGoodDecoupled)
  obtain ⟨recoveryBuffer, hRecoveryBuffer⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      (daiLiFiniteSubsystem buffer) hBufferSmall
  let retainedSubsystem := unionSubsystem
    (daiLiFiniteSubsystem goodLower) (daiLiFiniteSubsystem goodUpper)
  let bufferSubsystem := daiLiFiniteSubsystem buffer
  have hBoundary : P.fixedGeneratorOuterBoundary
      (retainedSubsystem.selected : Set ι) ⊆ (bufferSubsystem.selected : Set ι) := by
    change P.fixedGeneratorOuterBoundary (retained : Set ι) ⊆ (buffer : Set ι)
    simpa [retained, buffer, Set.union_assoc] using
      (fixedGeneratorOuterBoundary_horizontal_goodSides_subset P embedding ell region hAvoid)
  obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
    exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset P
      retainedSubsystem bufferSubsystem recoveryRetained recoveryBuffer
      (by simpa [retainedSubsystem] using hRecoveryRetained)
      hRecoveryBuffer hBoundary
  have hParentSubset : region ⊆ (unionSubsystem retainedSubsystem bufferSubsystem).selected := by
    change region ⊆ retained ∪ buffer
    intro q hq
    by_cases hqRetained : q ∈ retained
    · apply Finset.mem_union_left
      simpa [retainedSubsystem, retained, daiLiFiniteSubsystem] using hqRetained
    · apply Finset.mem_union_right
      have hqBuffer : q ∈ buffer := by
        apply Finset.mem_union_left
        apply daiLiHorizontal_unretained_subset_strip_union_endpoints P embedding ell region hAvoid
        exact Finset.mem_sdiff.mpr ⟨hq, hqRetained⟩
      exact hqBuffer
  exact exists_erasureRecovery_daiLiFiniteSubsystem_subset region
    (unionSubsystem retainedSubsystem bufferSubsystem).selected hParentSubset P
    ⟨recoveryExpanded, hRecoveryExpanded⟩
private theorem daiLiThreshold_le_sqrt_region_div_eight
    {d root region : Nat} (hd : 0 < d) (hRoot : d ≤ root) (hRegion : d ≤ region) :
    (d : ℝ) / (200 * Real.sqrt root) ≤ Real.sqrt region / 8 := by
  have hRootPositive : 0 < (root : ℝ) := by exact_mod_cast (lt_of_lt_of_le hd hRoot)
  have hRootSqrtPositive : 0 < Real.sqrt (root : ℝ) := Real.sqrt_pos.2 hRootPositive
  have hDroot : (d : ℝ) ≤ root := by exact_mod_cast hRoot
  have hDregion : (d : ℝ) ≤ region := by exact_mod_cast hRegion
  have hdNonneg : 0 ≤ (d : ℝ) := by positivity
  have hSq : (d : ℝ) ^ 2 ≤ (root : ℝ) * region := by
    calc
      (d : ℝ) ^ 2 = (d : ℝ) * d := by ring
      _ ≤ (root : ℝ) * d := mul_le_mul_of_nonneg_right hDroot hdNonneg
      _ ≤ (root : ℝ) * region := mul_le_mul_of_nonneg_left hDregion (by positivity)
  have hRootSq : (Real.sqrt (root : ℝ)) ^ 2 = (root : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hRegionSq : (Real.sqrt (region : ℝ)) ^ 2 = (region : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hProduct : (d : ℝ) ≤ Real.sqrt root * Real.sqrt region := by
    have hProductNonneg : 0 ≤ Real.sqrt (root : ℝ) * Real.sqrt region := by positivity
    nlinarith
  have hDiv : (d : ℝ) / (200 * Real.sqrt root) ≤
      (Real.sqrt root * Real.sqrt region) / (200 * Real.sqrt root) := by
    exact div_le_div_of_nonneg_right hProduct (by positivity)
  calc
    (d : ℝ) / (200 * Real.sqrt root) ≤
        (Real.sqrt root * Real.sqrt region) / (200 * Real.sqrt root) := hDiv
    _ = Real.sqrt region / 200 := by
      field_simp [hRootSqrtPositive.ne']
    _ ≤ Real.sqrt region / 8 := by
      have : 0 ≤ Real.sqrt (region : ℝ) := Real.sqrt_nonneg _
      nlinarith
private theorem daiLiRecursivePotential_le_four_fifths_distance
    {ell : ℝ} {d root region : Nat}
    (hEll : 0 ≤ ell) (hRootPositive : 0 < root)
    (hScale : ell = (d : ℝ) / (200 * Real.sqrt root)) :
    daiLiRecursivePotential ell root region ≤ 4 * (d : ℝ) / 5 := by
  have hRootSqrtPositive : 0 < Real.sqrt (root : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hRootPositive)
  have hRegionSqrt : 0 ≤ Real.sqrt (region : ℝ) := Real.sqrt_nonneg _
  have hRaw : daiLiRecursivePotential ell root region ≤
      160 * ell * Real.sqrt root := by
    unfold daiLiRecursivePotential
    nlinarith
  calc
    daiLiRecursivePotential ell root region ≤ 160 * ell * Real.sqrt root := hRaw
    _ = 4 * (d : ℝ) / 5 := by
      rw [hScale]
      field_simp [hRootSqrtPositive.ne']
      ring
private theorem daiLiRecursiveBuffer_card_lt_distance
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d root : Nat) (ell : ℝ)
    (hDistancePositive : 0 < d) (hRootPositive : 0 < root)
    (hEll : 0 ≤ ell)
    (hScale : ell = (d : ℝ) / (200 * Real.sqrt root))
    (region strip : Finset ι) (hRegionRoot : region.card ≤ root)
    (hStrip : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card)
    (hCounter : 10 * regionInteractionCounter P embedding ell region ≤ d)
    (hExterior : ((daiLiGoodExteriorNeighbors P embedding ell region).card : ℝ) ≤
      daiLiRecursivePotential ell root region.card) :
    ((strip ∪ (region ∩ longInteractionEndpointQubits P embedding ell)) ∪
      daiLiGoodExteriorNeighbors P embedding ell region).card < d := by
  let endpoints := region ∩ longInteractionEndpointQubits P embedding ell
  let exterior := daiLiGoodExteriorNeighbors P embedding ell region
  have hEndpoint : endpoints.card ≤ regionInteractionCounter P embedding ell region := by
    simpa [endpoints] using
      card_region_inter_longInteractionEndpoints_le_counter P embedding ell region
  have hUnionNat : ((strip ∪ endpoints) ∪ exterior).card ≤
      strip.card + endpoints.card + exterior.card := by
    calc
      _ ≤ (strip ∪ endpoints).card + exterior.card := Finset.card_union_le _ _
      _ ≤ (strip.card + endpoints.card) + exterior.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by omega
  have hUnionReal : (((strip ∪ endpoints) ∪ exterior).card : ℝ) ≤
      (strip.card : ℝ) + endpoints.card + exterior.card := by
    exact_mod_cast hUnionNat
  have hCounterReal : (regionInteractionCounter P embedding ell region : ℝ) ≤
      (d : ℝ) / 10 := by
    have hCounterCast : (10 : ℝ) *
        (regionInteractionCounter P embedding ell region : ℝ) ≤ d := by
      exact_mod_cast hCounter
    nlinarith
  have hSqrtMono : Real.sqrt (region.card : ℝ) ≤ Real.sqrt (root : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hRegionRoot)
  have hStripRoot : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt root := by
    calc
      (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card := hStrip
      _ ≤ 8 * ell * Real.sqrt root := by
        have hScaleNonneg : 0 ≤ 8 * ell := by positivity
        exact mul_le_mul_of_nonneg_left hSqrtMono hScaleNonneg
  have hRootSqrtPositive : 0 < Real.sqrt (root : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hRootPositive)
  have hStripBudget : 8 * ell * Real.sqrt root = (d : ℝ) / 25 := by
    rw [hScale]
    field_simp [hRootSqrtPositive.ne']
    ring
  have hPotentialBudget := daiLiRecursivePotential_le_four_fifths_distance
    (d := d) (region := region.card) hEll hRootPositive hScale
  have hTotal : (((strip ∪ endpoints) ∪ exterior).card : ℝ) ≤
      47 * (d : ℝ) / 50 := by
    have hEndpointReal : (endpoints.card : ℝ) ≤
        (regionInteractionCounter P embedding ell region : ℝ) := by
      exact_mod_cast hEndpoint
    have hExterior' : (exterior.card : ℝ) ≤
        daiLiRecursivePotential ell root region.card := by
      simpa [exterior] using hExterior
    rw [hStripBudget] at hStripRoot
    linarith
  have hStrict : 47 * (d : ℝ) / 50 < d := by
    have : (0 : ℝ) < d := by exact_mod_cast hDistancePositive
    linarith
  have hCard : ((strip ∪ endpoints) ∪ exterior).card < d := by
    exact_mod_cast (hTotal.trans_lt hStrict)
  simpa [endpoints, exterior] using hCard
private theorem exists_erasureRecovery_daiLiRecursiveSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d root : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hDistancePositive : 0 < d) (hTenDistance : 10 ≤ d) (hDistanceLeRoot : d ≤ root)
    (ell : ℝ) (hEll : 1 ≤ ell)
    (hScale : ell = (d : ℝ) / (200 * Real.sqrt root))
    (region : Finset ι) (hRegionRoot : region.card ≤ root)
    (hCounter : 10 * regionInteractionCounter P embedding ell region ≤ d)
    (hExterior : ((daiLiGoodExteriorNeighbors P embedding ell region).card : ℝ) ≤
      daiLiRecursivePotential ell root region.card) :
    ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
      (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
        P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery := by
  let statement : Nat → Prop := fun size =>
    ∀ region : Finset ι, region.card ≤ size → region.card ≤ root →
      10 * regionInteractionCounter P embedding ell region ≤ d →
      ((daiLiGoodExteriorNeighbors P embedding ell region).card : ℝ) ≤
        daiLiRecursivePotential ell root region.card →
      ∃ recovery : QuantumChannel (daiLiFiniteSubsystem region).complementSystem
        (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) (daiLiFiniteSubsystem region).complementSystem
          P.semanticCode (daiLiFiniteSubsystem region).erasureChannelFromRegister recovery
  have hStatement : ∀ size, statement size := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro region hSize hRegionRoot hCounter hExterior
      have hEllNonneg : 0 ≤ ell := by linarith
      by_cases hSmall : region.card < d
      · exact semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
          (daiLiFiniteSubsystem region) (by simpa [daiLiFiniteSubsystem] using hSmall)
      · have hRegionLarge : d ≤ region.card := Nat.le_of_not_gt hSmall
        have hRegionNonempty : region.Nonempty :=
          Finset.card_pos.mp (lt_of_lt_of_le hDistancePositive hRegionLarge)
        have hRegionTen : 10 ≤ region.card := hTenDistance.trans hRegionLarge
        have hPlaneScale : ell ≤ Real.sqrt region.card / 8 := by
          rw [hScale]
          exact daiLiThreshold_le_sqrt_region_div_eight hDistancePositive
            hDistanceLeRoot hRegionLarge
        rcases exists_daiLiPlaneSeparator embedding region hRegionNonempty hRegionTen
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hEll) hPlaneScale with
          hVertical | hHorizontal
        · rcases hVertical with ⟨lowerCut, upperCut, hAvoid, hWidth, hStrip,
            hLowerBalanced, hUpperBalanced⟩
          let lower := daiLiVerticalSeparatorLower embedding region lowerCut
          let upper := daiLiVerticalSeparatorUpper embedding region upperCut
          let strip := daiLiVerticalSeparatorStrip embedding region lowerCut upperCut
          have hLowerSubset : lower ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hUpperSubset : upper ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hLowerRoot : lower.card ≤ root :=
            (Finset.card_le_card hLowerSubset).trans hRegionRoot
          have hUpperRoot : upper.card ≤ root :=
            (Finset.card_le_card hUpperSubset).trans hRegionRoot
          have hLowerCounter : 10 * regionInteractionCounter P embedding ell lower ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hLowerSubset)).trans hCounter
          have hUpperCounter : 10 * regionInteractionCounter P embedding ell upper ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hUpperSubset)).trans hCounter
          have hLowerBalanced' : 10 * lower.card ≤ 9 * region.card := by
            simpa [lower] using hLowerBalanced
          have hUpperBalanced' : 10 * upper.card ≤ 9 * region.card := by
            simpa [upper] using hUpperBalanced
          have hLowerLt : lower.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hUpperLt : upper.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hStrip' : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card := by
            simpa [strip] using hStrip
          have hLowerExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                daiLiRecursivePotential ell root lower.card := by
            have hSubset := daiLiGoodExteriorNeighbors_vertical_lower_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell lower).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root lower.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hLowerBalanced']
          have hUpperExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                daiLiRecursivePotential ell root upper.card := by
            have hSubset := daiLiGoodExteriorNeighbors_vertical_upper_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell upper).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root upper.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hUpperBalanced']
          have hLowerRecovery := ih lower.card (lt_of_lt_of_le hLowerLt hSize) lower
            le_rfl hLowerRoot hLowerCounter hLowerExterior
          have hUpperRecovery := ih upper.card (lt_of_lt_of_le hUpperLt hSize) upper
            le_rfl hUpperRoot hUpperCounter hUpperExterior
          have hBufferSmall := daiLiRecursiveBuffer_card_lt_distance P embedding d root ell
            hDistancePositive (lt_of_lt_of_le hDistancePositive hDistanceLeRoot) hEllNonneg hScale
            region strip hRegionRoot hStrip' hCounter hExterior
          exact exists_erasureRecovery_of_daiLiVerticalRecursiveStep P embedding d hDistance
            ell region hEllNonneg hAvoid hWidth.le
            (by simpa [lower] using hLowerRecovery)
            (by simpa [upper] using hUpperRecovery)
            (by simpa [strip] using hBufferSmall)
        · rcases hHorizontal with ⟨lowerCut, upperCut, hAvoid, hWidth, hStrip,
            hLowerBalanced, hUpperBalanced⟩
          let lower := daiLiHorizontalSeparatorLower embedding region lowerCut
          let upper := daiLiHorizontalSeparatorUpper embedding region upperCut
          let strip := daiLiHorizontalSeparatorStrip embedding region lowerCut upperCut
          have hLowerSubset : lower ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hUpperSubset : upper ⊆ region := by
            intro q hq
            exact (Finset.mem_filter.mp hq).1
          have hLowerRoot : lower.card ≤ root :=
            (Finset.card_le_card hLowerSubset).trans hRegionRoot
          have hUpperRoot : upper.card ≤ root :=
            (Finset.card_le_card hUpperSubset).trans hRegionRoot
          have hLowerCounter : 10 * regionInteractionCounter P embedding ell lower ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hLowerSubset)).trans hCounter
          have hUpperCounter : 10 * regionInteractionCounter P embedding ell upper ≤ d := by
            exact (Nat.mul_le_mul_left 10
              (regionInteractionCounter_mono P embedding ell hUpperSubset)).trans hCounter
          have hLowerBalanced' : 10 * lower.card ≤ 9 * region.card := by
            simpa [lower] using hLowerBalanced
          have hUpperBalanced' : 10 * upper.card ≤ 9 * region.card := by
            simpa [upper] using hUpperBalanced
          have hLowerLt : lower.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hUpperLt : upper.card < region.card := by
            have hPositive : 0 < region.card := Finset.card_pos.mpr hRegionNonempty
            omega
          have hStrip' : (strip.card : ℝ) ≤ 8 * ell * Real.sqrt region.card := by
            simpa [strip] using hStrip
          have hLowerExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                daiLiRecursivePotential ell root lower.card := by
            have hSubset := daiLiGoodExteriorNeighbors_horizontal_lower_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell lower).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell lower).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root lower.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hLowerBalanced']
          have hUpperExterior :
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                daiLiRecursivePotential ell root upper.card := by
            have hSubset := daiLiGoodExteriorNeighbors_horizontal_upper_subset
              P embedding ell region hAvoid hWidth.le
            have hCardNat : (daiLiGoodExteriorNeighbors P embedding ell upper).card ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)
            have hCardReal : ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := by
              exact_mod_cast hCardNat
            calc
              ((daiLiGoodExteriorNeighbors P embedding ell upper).card : ℝ) ≤
                  strip.card + (daiLiGoodExteriorNeighbors P embedding ell region).card := hCardReal
              _ ≤ 8 * ell * Real.sqrt region.card +
                  daiLiRecursivePotential ell root region.card :=
                add_le_add hStrip' hExterior
              _ ≤ daiLiRecursivePotential ell root upper.card := by
                nlinarith [daiLiRecursivePotential_step (root := root)
                  hEllNonneg hUpperBalanced']
          have hLowerRecovery := ih lower.card (lt_of_lt_of_le hLowerLt hSize) lower
            le_rfl hLowerRoot hLowerCounter hLowerExterior
          have hUpperRecovery := ih upper.card (lt_of_lt_of_le hUpperLt hSize) upper
            le_rfl hUpperRoot hUpperCounter hUpperExterior
          have hBufferSmall := daiLiRecursiveBuffer_card_lt_distance P embedding d root ell
            hDistancePositive (lt_of_lt_of_le hDistancePositive hDistanceLeRoot) hEllNonneg hScale
            region strip hRegionRoot hStrip' hCounter hExterior
          exact exists_erasureRecovery_of_daiLiHorizontalRecursiveStep P embedding d hDistance
            ell region hEllNonneg hAvoid hWidth.le
            (by simpa [lower] using hLowerRecovery)
            (by simpa [upper] using hUpperRecovery)
            (by simpa [strip] using hBufferSmall)
  exact hStatement region.card region le_rfl hRegionRoot hCounter hExterior
private theorem encodedQubits_eq_zero_of_daiLiFullRecovery
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d) (hd : 0 < d)
    (recoveryAll : QuantumChannel
      (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem
      (Qubit.QubitRegister ι))
    (hRecoveryAll : Correctable (Qubit.QubitRegister ι)
      (daiLiFiniteSubsystem (Finset.univ : Finset ι)).complementSystem P.semanticCode
      (daiLiFiniteSubsystem (Finset.univ : Finset ι)).erasureChannelFromRegister
        recoveryAll) :
    P.encodedQubits = 0 := by
  let allSubsystem : FiniteSubsystem ι :=
    daiLiFiniteSubsystem (Finset.univ : Finset ι)
  let emptySubsystem : FiniteSubsystem ι := daiLiFiniteSubsystem (∅ : Finset ι)
  obtain ⟨recoveryEmpty, hRecoveryEmpty⟩ :=
    semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
      emptySubsystem (by
        change 0 < d
        exact hd)
  have hBound := two_correctable_regions_encodedQubits_le_separator_card P
    allSubsystem emptySubsystem emptySubsystem
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    (by simp [emptySubsystem, daiLiFiniteSubsystem])
    (by simp [allSubsystem, emptySubsystem, daiLiFiniteSubsystem])
    recoveryAll (by simpa [allSubsystem] using hRecoveryAll)
    recoveryEmpty hRecoveryEmpty
  simpa [emptySubsystem, daiLiFiniteSubsystem] using hBound
private theorem encodedQubits_le_blockLength
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _
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
    (hAboveBPT : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2)
    (hLargeDistance : Real.sqrt ((P.encodedQubits : ℝ) * (Fintype.card ι : ℝ)) ≤ d)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) :
    P.encodedQubits = 0 := by
  by_contra hNonzero
  have hEncodedPositive : 0 < P.encodedQubits := Nat.pos_of_ne_zero hNonzero
  have hEncodedLeBlock : P.encodedQubits ≤ Fintype.card ι :=
    encodedQubits_le_blockLength P
  have hBlockPositive : 0 < Fintype.card ι :=
    lt_of_lt_of_le hEncodedPositive hEncodedLeBlock
  have hDistancePositive : 0 < d := by
    by_contra hDistanceNonpositive
    have hdZero : d = 0 := Nat.eq_zero_of_not_pos hDistanceNonpositive
    simp [hdZero] at hAboveBPT
    omega
  have hTenDistance : 10 ≤ d := by
    have hScaled : 100 * Fintype.card ι ≤ Fintype.card ι * d ^ 2 := by
      calc
        100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2 := hAboveBPT
        _ ≤ Fintype.card ι * d ^ 2 :=
          Nat.mul_le_mul_right (d ^ 2) hEncodedLeBlock
    have hSquared : 100 ≤ d ^ 2 := by
      exact Nat.le_of_mul_le_mul_left
        (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hScaled)
        hBlockPositive
    by_contra hTen
    have hNine : d ≤ 9 := by omega
    interval_cases d <;> norm_num at hSquared
  by_cases hDistanceLeBlock : d ≤ Fintype.card ι
  · let ell := daiLiLargeDistanceThreshold d (Fintype.card ι)
    have hEll : 1 ≤ ell := by
      dsimp [ell]
      exact one_le_daiLiLargeDistanceThreshold_of_positive_encodedQubits
        P embedding d hDistance hFew (by omega) hEncodedPositive
    have hCounter : 10 * regionInteractionCounter P embedding ell (Finset.univ : Finset ι) ≤ d := by
      simpa [ell] using daiLiLargeDistance_regionIncidence_budget P embedding d hFew
        (Finset.univ : Finset ι)
    have hExteriorEmpty : daiLiGoodExteriorNeighbors P embedding ell
        (Finset.univ : Finset ι) = ∅ := by
      simp [daiLiGoodExteriorNeighbors]
    have hExterior :
        ((daiLiGoodExteriorNeighbors P embedding ell (Finset.univ : Finset ι)).card : ℝ) ≤
          daiLiRecursivePotential ell (Fintype.card ι) (Finset.univ : Finset ι).card := by
      simp [hExteriorEmpty, daiLiRecursivePotential]
    obtain ⟨recoveryAll, hRecoveryAll⟩ :=
      exists_erasureRecovery_daiLiRecursiveSeparator P embedding d (Fintype.card ι)
        hDistance hDistancePositive hTenDistance hDistanceLeBlock ell hEll
        (by rfl) (Finset.univ : Finset ι) (by simp) hCounter hExterior
    exact hNonzero (encodedQubits_eq_zero_of_daiLiFullRecovery P d hDistance
      hDistancePositive recoveryAll hRecoveryAll)
  · have hBlockLtDistance : Fintype.card ι < d := Nat.lt_of_not_ge hDistanceLeBlock
    obtain ⟨recoveryAll, hRecoveryAll⟩ :=
      semanticStabilizerDistance_erasureRecoverableFromRegister P.code d hDistance
        (daiLiFiniteSubsystem (Finset.univ : Finset ι)) (by
          simpa [daiLiFiniteSubsystem] using hBlockLtDistance)
    exact hNonzero (encodedQubits_eq_zero_of_daiLiFullRecovery P d hDistance
      hDistancePositive recoveryAll hRecoveryAll)
end QEC.Locality
