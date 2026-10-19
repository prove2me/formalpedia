-- Prove2me | solution 1 for SoficGroups.KunActualSourceURetainedNoPremise.exists_actual_source_u_retained_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/e16f83ce-d721-4f78-bf35-bb746ff1b528

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunUnconditionalActualSourceDecomposition_exists_unconditional_actual_source_dual_finpartition_sequences
import Theorems.Thm_SoficGroups_SourceRetainedActualMatching_retained_source_transport_matching_of_ambient_midrank_variance
import Theorems.Thm_SoficGroups_KunActualBothTransportedOverlapScales_exists_source_both_capped_overlap_scales
import Theorems.Thm_SoficGroups_KunLiteralNineSourceCompletedCentralizerModels_exists_source_common_log_rank_with_ambient_midrank_variance

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSourceURetainedNoPremise
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunActualSourceURetainedNoPremise
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) :
    ∃ (SΓ : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
      (QΓ : (n : ℕ) →
        Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
      (γΓ : ℝ)
      (H eta r : ℕ → ℝ)
      (R : (n : ℕ) → Finset (Finset (Fin (A.model n).size))),
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤ ∧
      0 < γΓ ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ n, 0 < H n) ∧
      Tendsto H atTop (𝓝 0) ∧
      (∀ n, 0 < eta n) ∧
      (∀ n, eta n < 1) ∧
      Tendsto eta atTop (𝓝 0) ∧
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      (∀ n,
        R n =
          SoficGroups.SourceRetainedActualMatching.retainedTransportedComponents
            (QΓ n)
            ((A.model n).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)
            (H n) (r n) (eta n)) ∧
      (∀ n,
        R n ⊆
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)).parts) ∧
      (∀ n C, C ∈ R n →
        SoficGroups.maximumOverlapPart (QΓ n) C ∈ (QΓ n).parts) ∧
      (∀ n, eta n ≤ (1 : ℝ) / 2 →
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
          ∀ C, C ∈ R n →
            (SoficGroups.maximumOverlapPart (QΓ n) C).card <
              2 * (C ∩ SoficGroups.maximumOverlapPart
                (QΓ n) C).card) ∧
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (Fin (A.model n).size)) \
            SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          ((∑ C ∈ R n,
            (C ∆ SoficGroups.maximumOverlapPart
              (QΓ n) C).card : ℕ) : ℝ) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ n, 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        Set.InjOn (SoficGroups.maximumOverlapPart (QΓ n))
          ((R n : Finset (Finset (Fin (A.model n).size))) :
            Set (Finset (Fin (A.model n).size)))) := by
  classical
  obtain ⟨SΓ, SG, QΓ, QG, γΓ, γG, _hSG,
      honeΓ, hsymmetricΓ, hgeneratesΓ,
      _honeG, hsymmetricG, hgeneratesG,
      _hfaithful, hpositive,
      hγΓ, hγG, hexpandΓ, hexpandG,
      hboundaryΓ, hboundaryG⟩ :=
    SoficGroups.KunUnconditionalActualSourceDecomposition.exists_unconditional_actual_source_dual_finpartition_sequences A
  have hexpandΓ' :
      ∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ) :=
    hexpandΓ
  have hboundaryΓ' :
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) :=
    hboundaryΓ
  obtain ⟨eta, H, hetapos, hetaone, _hetaanti, hetazero,
      hHpos, _hHanti, hHzero, hratio, hoverlap, hloss⟩ :=
    SoficGroups.KunActualBothTransportedOverlapScales.exists_source_both_capped_overlap_scales
        A SΓ hsymmetricΓ hgeneratesΓ QΓ γΓ hγΓ
        hexpandΓ' hboundaryΓ'
  have hoverlap' :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈ SoficGroups.insufficientOverlapComponents
            (SoficGroups.transportedUnivFinpartition
              (QΓ n)
              ((A.model n).action
                (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                  j)))
            (QΓ n) (eta n), (C.card : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) :=
    hoverlap
  have hloss' :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (SoficGroups.transportedUnivFinpartition
              (QΓ n)
              ((A.model n).action
                (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                  j))).parts,
            ((C.card : ℝ) -
              ((C ∩ SoficGroups.maximumOverlapPart
                (QΓ n) C).card : ℝ))) /
                (A.model n).size)
        atTop (𝓝 0) :=
    hloss
  obtain ⟨r, hr, hvariance, hinverse⟩ :=
    SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.exists_source_common_log_rank_with_ambient_midrank_variance
        A SΓ SG QΓ QG γG
        hsymmetricG hgeneratesG hpositive hγG hexpandG
        hboundaryΓ hboundaryG eta H
        (fun n => (hetapos n).le) hetaone hHpos
        hetazero hratio hoverlap' hloss'
  letI : ∀ n, Nonempty (Fin (A.model n).size) :=
    fun n => Fin.pos_iff_nonempty.mp (A.model n).size_pos
  let T : (n : ℕ) → Fin 2 → Equiv.Perm (Fin (A.model n).size) :=
    fun n j =>
      (A.model n).action
        (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)
  have hvariance' :
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (C.card : ℝ) *
              SoficGroups.midrankVariance
                (SoficGroups.componentRankMassList C
                  (SoficGroups.SourceRetainedActualMatching.logarithmicComponentRank
                    (QΓ n) (H n) (r n)))) /
              Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    simpa only [
      SoficGroups.SourceRetainedActualMatching.logarithmicComponentRank,
      SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank,
      SoficGroups.SourceCommonOffsetMidrankEnergy.realComponentSize,
      Fintype.card_fin] using hvariance
  have hinverse' :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          ((SoficGroups.partitionWordCrossing
            (QG n) (T n j).symm).card : ℝ) /
              Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    intro j
    simpa only [T, Fintype.card_fin, Equiv.Perm.inv_def,
      SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable,
      SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement,
      SoficGroups.SourceBothCompressionNormalization.sourceCompressionVElement,
      SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable,
      SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionU,
      SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionV]
      using hinverse j
  have hoverlapNat :
      ∀ j : Fin 2, Tendsto
        (fun n =>
          ((∑ C ∈ SoficGroups.insufficientOverlapComponents
            (SoficGroups.transportedUnivFinpartition
              (QΓ n) (T n j))
            (QΓ n) (eta n), C.card : ℕ) : ℝ) /
              Fintype.card (Fin (A.model n).size))
        atTop (𝓝 0) := by
    intro j
    simpa only [T, Nat.cast_sum, Fintype.card_fin] using hoverlap j
  have hmatch :=
    SoficGroups.SourceRetainedActualMatching.retained_source_transport_matching_of_ambient_midrank_variance
        (fun n => Fin (A.model n).size)
        (Fin 2) QΓ QG T H r eta hHpos hHzero
        (fun n => (hetapos n).le) hetazero
        hvariance' hinverse' hoverlapNat (0 : Fin 2)
  have hTzero (n : ℕ) :
      T n (0 : Fin 2) =
        (A.model n).action
          SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement :=
    rfl
  let R : (n : ℕ) → Finset (Finset (Fin (A.model n).size)) :=
    fun n =>
      SoficGroups.SourceRetainedActualMatching.retainedTransportedComponents
        (QΓ n)
        ((A.model n).action
          SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)
        (H n) (r n) (eta n)
  obtain ⟨hparts, htarget, hmajor, hdiscard, hsymmetric, hinjective⟩ :=
    hmatch
  refine ⟨SΓ, QΓ, γΓ, H, eta, r, R,
    honeΓ, hsymmetricΓ, hgeneratesΓ, hγΓ,
    hexpandΓ', hboundaryΓ', hHpos, hHzero,
    hetapos, hetaone, hetazero, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · simpa only [R, hTzero] using hparts
  · simpa only [R, hTzero] using htarget
  · simpa only [R, hTzero] using hmajor
  · simpa only [R, hTzero, Fintype.card_fin] using hdiscard
  · simpa only [R, hTzero, Fintype.card_fin] using hsymmetric
  · simpa only [R, hTzero] using hinjective
end SoficGroups.KunActualSourceURetainedNoPremise
