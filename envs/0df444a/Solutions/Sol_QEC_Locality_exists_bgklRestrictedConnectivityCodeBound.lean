-- Prove2me | solution 1 for QEC.Locality.exists_bgklRestrictedConnectivityCodeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:31:46.906132+00:00
-- url     : https://prove2.me/submissions/8bb3edf7-8054-49f3-b62a-60b3fdda4c1b

import Definitions.Def_QEC_Locality_CorrectablePartition_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Results_LocalityBounds_RestrictedConnectivity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_exists_bkRecursiveSeparatorPartition
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_card_le_bkSumPreservingRecurrence
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_bkRpowCoefficient_nonneg
import Theorems.Thm_QEC_Locality_bkRpowGap_pos
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
import Theorems.Thm_QEC_Locality_exists_bgklCorrectablePartition
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
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
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
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
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
private theorem bkRpowCoefficient_pos
    {beta c : ℝ} (hbeta : 0 < beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < bkRpowCoefficient beta c := by
  unfold bkRpowCoefficient
  exact div_pos hbeta
    (mul_pos (bkRpowGap_pos hc0 hc1)
      (Real.rpow_pos_of_pos (by norm_num) _))
private theorem encodedQubits_le_blockLength
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.encodedQubits ≤ Fintype.card ι := by
  rw [P.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _
private theorem bgkl_endpoint_one_bound
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) :
    (P.encodedQubits : ℝ) * Real.rpow d ((1 - (1 : ℝ) ^ 2) / 1) ≤
      Fintype.card ι := by
  have hdimension : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast encodedQubits_le_blockLength P
  simpa using hdimension
private theorem exists_bgklRestrictedConnectivityCodeBound_of_two_le
    (beta c : ℝ) (hbeta : 1 ≤ beta) (hc : 0 < c ∧ c ≤ 1) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        {κ : Type v} [Fintype κ]
        (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
        (d : Nat), 2 ≤ d → d ≤ Fintype.card ι →
        StabilizerCode.SemanticStabilizerDistance P.code d →
        P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta c →
        (P.encodedQubits : ℝ) *
          Real.rpow d ((1 - c ^ 2) / c) ≤ alpha * Fintype.card ι := by
  by_cases hcOne : c = 1
  · subst c
    refine ⟨1, by norm_num, ?_⟩
    intro ι instFintype instDecidableEq κ instFintypeK P d _hd _hdn _hDistance _hProfile
    simpa using bgkl_endpoint_one_bound P d
  have hcLt : c < 1 := lt_of_le_of_ne hc.2 hcOne
  rcases exists_bgklCorrectablePartition beta c hbeta ⟨hc.1, hcLt⟩ with
    ⟨partitionAlpha, hpartitionAlphaPos, hpartition⟩
  let recurrenceAlpha := bkRpowCoefficient beta c
  have hbetaNonneg : 0 ≤ beta := by linarith
  refine ⟨partitionAlpha * recurrenceAlpha,
    mul_pos hpartitionAlphaPos
      (bkRpowCoefficient_pos (zero_lt_one.trans_le hbeta) hc.1.le hcLt), ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK P d hd hdn hDistance hProfile
  rcases hpartition P d (Nat.zero_lt_two.trans_le hd) hdn hDistance hProfile with
    ⟨A, recoveryA, hRecoveryA, hAComplement⟩
  let ARegion : FiniteSubsystem ι := finiteSubsystemOfFinset A
  let remaining : Finset ι := Finset.univ \ A
  have hremainingCard : (remaining.card : ℝ) ≤
      partitionAlpha * Fintype.card ι / Real.rpow d ((1 - c) / c) := by
    simpa [remaining] using hAComplement
  have hdPos : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_two.trans_le hd)
  have hfirstPowerPos : 0 < Real.rpow d ((1 - c) / c) :=
    Real.rpow_pos_of_pos hdPos _
  have hsecondPowerPos : 0 < Real.rpow d (1 - c) :=
    Real.rpow_pos_of_pos hdPos _
  have htargetPower : ((1 - c ^ 2) / c) = (1 - c) / c + (1 - c) := by
    field_simp [ne_of_gt hc.1]
    ring
  by_cases hdRemaining : d ≤ remaining.card
  · rcases P.exists_bkRecursiveSeparatorPartition d hDistance
        (Nat.zero_lt_two.trans_le hd) remaining with ⟨partition, recoveryB, hRecoveryB⟩
    let BRegion := bgklBKPartitionRegion partition
    let CRegion : FiniteSubsystem ι := ⟨partition.remainder⟩
    have hBSubset : BRegion.selected ⊆ remaining := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨piece, hpiece, hxpiece⟩
      exact partition.piece_subset piece hpiece hxpiece
    have hCSubset : CRegion.selected ⊆ remaining := partition.remainder_subset
    have hAB : Disjoint ARegion.selected BRegion.selected := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp (hBSubset hxB)).2 hxA
    have hAC : Disjoint ARegion.selected CRegion.selected := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxC
      exact (Finset.mem_sdiff.mp (hCSubset hxC)).2 hxA
    have hBC : Disjoint BRegion.selected CRegion.selected := by
      exact partition.pieces_remainder_disjoint
    have hCover : ARegion.selected ∪ BRegion.selected ∪ CRegion.selected = Finset.univ := by
      change A ∪ partition.pieces.biUnion id ∪ partition.remainder = Finset.univ
      rw [Finset.union_assoc, partition.covers]
      exact Finset.union_sdiff_of_subset (Finset.subset_univ A)
    have hdimension : P.encodedQubits ≤ CRegion.selected.card :=
      two_correctable_regions_encodedQubits_le_separator_card P ARegion BRegion CRegion hAB hAC hBC
        hCover recoveryA (by simpa [ARegion] using hRecoveryA) recoveryB
        hRecoveryB
    have hprofileRange : ∀ scale : Nat, d ≤ scale → scale ≤ remaining.card →
        (twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale : ℝ) ≤
          beta * Real.rpow scale c := by
      intro scale hdscale hscale
      have hscalePos : 1 ≤ scale := by omega
      exact hProfile.2.2.2 scale hscalePos
        (hscale.trans (Finset.card_le_card Finset.sdiff_subset))
    have hrecurrence : (partition.remainder.card : ℝ) ≤
        recurrenceAlpha * remaining.card / Real.rpow d (1 - c) := by
      have hcharge : partition.remainder.card ≤
          bkSumPreservingRecurrence P.fixedGeneratorInteractionGraph d remaining.card := by
        simpa [remaining] using partition.remainder_card_le_bkSumPreservingRecurrence
      have hquantitative := bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
        P.fixedGeneratorInteractionGraph d remaining.card remaining.card beta c hbetaNonneg hc.1.le hcLt
        hd hdRemaining le_rfl hprofileRange
      have hchargeReal : (partition.remainder.card : ℝ) ≤
          (bkSumPreservingRecurrence P.fixedGeneratorInteractionGraph d remaining.card : ℝ) := by
        exact_mod_cast hcharge
      exact hchargeReal.trans hquantitative
    have hdimensionReal : (P.encodedQubits : ℝ) ≤ partition.remainder.card := by
      exact_mod_cast hdimension
    have hcoefficientNonneg : 0 ≤ recurrenceAlpha :=
      bkRpowCoefficient_nonneg hbetaNonneg hc.1.le hcLt
    have hscaledRemaining : recurrenceAlpha * (remaining.card : ℝ) /
        Real.rpow d (1 - c) ≤
        recurrenceAlpha * (partitionAlpha * Fintype.card ι /
          Real.rpow d ((1 - c) / c)) / Real.rpow d (1 - c) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hremainingCard hcoefficientNonneg) hsecondPowerPos.le
    have hbaseBound : (P.encodedQubits : ℝ) ≤
        (partitionAlpha * recurrenceAlpha) * Fintype.card ι /
          (Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c)) := by
      calc
        (P.encodedQubits : ℝ) ≤ partition.remainder.card := hdimensionReal
        _ ≤ recurrenceAlpha * remaining.card / Real.rpow d (1 - c) := hrecurrence
        _ ≤ recurrenceAlpha * (partitionAlpha * Fintype.card ι /
            Real.rpow d ((1 - c) / c)) / Real.rpow d (1 - c) := hscaledRemaining
        _ = (partitionAlpha * recurrenceAlpha) * Fintype.card ι /
            (Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c)) := by
          field_simp [hfirstPowerPos.ne', hsecondPowerPos.ne']
    have hproductPower : Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c) =
        Real.rpow d ((1 - c ^ 2) / c) := by
      calc
        Real.rpow d ((1 - c) / c) * Real.rpow d (1 - c) =
            Real.rpow d ((1 - c) / c + (1 - c)) :=
          (Real.rpow_add hdPos _ _).symm
        _ = Real.rpow d ((1 - c ^ 2) / c) := by rw [htargetPower]
    have htradeoff : (P.encodedQubits : ℝ) ≤
        (partitionAlpha * recurrenceAlpha) * Fintype.card ι /
          Real.rpow d ((1 - c ^ 2) / c) := by
      rw [hproductPower] at hbaseBound
      exact hbaseBound
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hdPos _)).mp at htradeoff
    rw [mul_assoc]
    simpa [mul_comm, mul_left_comm] using htradeoff
  · have hremainingSmall : remaining.card < d := Nat.lt_of_not_ge hdRemaining
    let BRegion : FiniteSubsystem ι := finiteSubsystemOfFinset remaining
    let CRegion : FiniteSubsystem ι := finiteSubsystemOfFinset ∅
    rcases semanticStabilizerDistance_erasureRecoverableFromRegister
      P.code d hDistance BRegion hremainingSmall with
      ⟨recoveryB, hRecoveryB⟩
    have hAB : Disjoint ARegion.selected BRegion.selected := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp hxB).2 hxA
    have hAC : Disjoint ARegion.selected CRegion.selected := by
      simp [ARegion, CRegion, finiteSubsystemOfFinset]
    have hBC : Disjoint BRegion.selected CRegion.selected := by
      simp [BRegion, CRegion, finiteSubsystemOfFinset]
    have hCover : ARegion.selected ∪ BRegion.selected ∪ CRegion.selected = Finset.univ := by
      change A ∪ (Finset.univ \ A) ∪ ∅ = Finset.univ
      rw [Finset.union_empty]
      exact Finset.union_sdiff_of_subset (Finset.subset_univ A)
    have hdimension : P.encodedQubits ≤ CRegion.selected.card :=
      two_correctable_regions_encodedQubits_le_separator_card P ARegion BRegion CRegion hAB hAC hBC
        hCover recoveryA (by simpa [ARegion] using hRecoveryA) recoveryB
        hRecoveryB
    have hzero : (P.encodedQubits : ℝ) = 0 := by
      have : P.encodedQubits = 0 := by
        exact Nat.eq_zero_of_le_zero (by simpa [CRegion, finiteSubsystemOfFinset] using hdimension)
      exact_mod_cast this
    rw [hzero, zero_mul]
    exact mul_nonneg (mul_nonneg hpartitionAlphaPos.le
      (bkRpowCoefficient_nonneg hbetaNonneg hc.1.le hcLt)) (Nat.cast_nonneg _)
namespace BGKLRestrictedConnectivityFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
end BGKLRestrictedConnectivityFamily
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (beta c : ℝ) (hbeta : 1 ≤ beta) (hc : 0 < c ∧ c ≤ 1) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        {κ : Type v} [Fintype κ]
        (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
        (d : Nat), 1 ≤ d → d ≤ Fintype.card ι →
        StabilizerCode.SemanticStabilizerDistance P.code d →
        P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta c →
        (P.encodedQubits : ℝ) *
          Real.rpow d ((1 - c ^ 2) / c) ≤ alpha * Fintype.card ι := by
  rcases exists_bgklRestrictedConnectivityCodeBound_of_two_le beta c hbeta hc with
    ⟨twoAlpha, htwoAlphaPos, htwoBound⟩
  refine ⟨max 1 twoAlpha, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK P d hd hdn hDistance hProfile
  by_cases hdOne : d = 1
  · subst d
    have hdimension : (P.encodedQubits : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast encodedQubits_le_blockLength P
    have hbase : (P.encodedQubits : ℝ) *
        ((↑(1 : Nat) : ℝ) ^ ((1 - c ^ 2) / c)) ≤ Fintype.card ι := by
      simpa using hdimension
    exact hbase.trans (by
      calc
        (Fintype.card ι : ℝ) = 1 * Fintype.card ι := by ring
        _ ≤ max 1 twoAlpha * Fintype.card ι :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  · have hdTwo : 2 ≤ d := by omega
    have hbase := htwoBound P d hdTwo hdn hDistance hProfile
    exact hbase.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
end QEC.Locality
