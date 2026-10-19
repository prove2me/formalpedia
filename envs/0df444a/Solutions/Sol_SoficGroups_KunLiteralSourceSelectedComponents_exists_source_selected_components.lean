-- Prove2me | solution 1 for SoficGroups.KunLiteralSourceSelectedComponents.exists_source_selected_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/3a100d3b-8855-45ea-9f5b-49426cf4ad08

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_u_transported_reference_half_expansion
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_u_transported_reference_boundary_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceGuardedCanonicalSelection_exists_source_guarded_canonical_selected_components_of_retained_matching
import Theorems.Thm_SoficGroups_KunActualSourceURetainedNoPremise_exists_actual_source_u_retained_matching

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunLiteralSourceSelectedComponents
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord)) :
    ∃ (S : Finset
          (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
      (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
      (hgenerates : Subgroup.closure
        (S : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤)
      (Q : (n : ℕ) →
        Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
      (gamma : ℝ) (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size)),
      1 ∈ S ∧
      0 < gamma ∧
      Tendsto
        (fun n =>
          (∑ D ∈ (Q n).parts,
            (SoficGroups.boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) D : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto r atTop atTop ∧
      (∀ n, C n ∈ (sourceTransportedPartition A Q (n + N)).parts) ∧
      (∀ n, (C n).Nonempty) ∧
      (∀ n, ∀ D : Finset (Fin (A.model (n + N)).size),
        D ⊆ C n → 2 * D.card ≤ (C n).card →
          gamma * (D.card : ℝ) ≤
            (SoficGroups.boundary
              (sourceTransportedReferenceGenerators A S (n + N)) D : ℝ)) ∧
      Tendsto
        (fun n =>
          (SoficGroups.boundary
            (sourceTransportedReferenceGenerators A S (n + N))
            (C n) : ℝ) / (C n).card)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (((C n ∩ SoficGroups.matchedRadiusBad
            (sourceTransportedPartition A Q (n + N))
            (sourceSelectedProductRadiusLabels S F (r n))
            (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action)
            (sourceSelectedRadiusBad A S
              hsymmetric hgenerates F (n + N) (r n))).card : ℝ) /
                (C n).card))
        atTop (𝓝 0) ∧
      Tendsto (fun n => (C n).card) atTop atTop := by
  classical
  obtain ⟨S, Q, gamma, H, eta, _offset, R,
      hone, hsymmetric, hgenerates, hgamma,
      hexpand, hsource, _hHpositive, hH,
      _hetapositive, _hetaone, heta, _hoffset, _hRdef,
      hR, htarget, hmajor, hdiscard, hsymm, _hinjective⟩ :=
    SoficGroups.KunActualSourceURetainedNoPremise.exists_actual_source_u_retained_matching A
  have hsource' :
      Tendsto
        (fun n =>
          (∑ D ∈ (Q n).parts,
            (SoficGroups.boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) D : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) := by
    exact hsource
  let P : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)) :=
    fun n => sourceTransportedPartition A Q n
  let sigma : (n : ℕ) → ↥S → Equiv.Perm (Fin (A.model n).size) :=
    fun n => sourceTransportedReferenceGenerators A S n
  let E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size) :=
    fun n _ => sourceGeneratorFamilyConjugacyBad A S n
  have hRP : ∀ n, R n ⊆ (P n).parts := by
    simpa only [P, sourceTransportedPartition,
      sourceCompressionPermutation] using hR
  have hE : ∀ k, Tendsto
      (fun n => ((E n k).card : ℝ) / (A.model n).size)
      atTop (𝓝 0) := by
    intro k
    simpa only [E] using
      sourceGeneratorFamilyConjugacyBad_density_tendsto_zero A S
  have hboundary : Tendsto
      (fun n =>
        (∑ D ∈ (P n).parts,
          (SoficGroups.boundary (sigma n) D : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0) := by
    change Tendsto
      (fun n =>
        (∑ D ∈
          (SoficGroups.transportedUnivFinpartition
            (Q n)
            ((A.model n).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                  SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion i) *
                ((A.model n).action
                  SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
            D : ℝ)) / (A.model n).size)
      atTop (𝓝 0)
    exact
      SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_boundary_density_tendsto_zero
        A S Q hsource'
  obtain ⟨N, r, C, _hN, _hetaguard, _hexpguard,
      hr, hCR, hCboundary, hCbad, hCgrowth⟩ :=
    SoficGroups.SourceGuardedCanonicalSelection.exists_source_guarded_canonical_selected_components_of_retained_matching
        A S hone hsymmetric hgenerates
        P Q sigma R hRP
        (fun n D => SoficGroups.maximumOverlapPart (Q n) D)
        htarget H eta hH heta hmajor hdiscard hsymm
        F E hE hsource' hboundary 0
  have hCpart (n : ℕ) :
      C n ∈ (sourceTransportedPartition A Q (n + N)).parts := by
    exact hRP (n + N) (hCR n)
  have hCnonempty (n : ℕ) : (C n).Nonempty :=
    (sourceTransportedPartition A Q (n + N)).nonempty_of_mem_parts
      (hCpart n)
  have hexpand' :
      ∀ n, ∀ D ∈ (Q n).parts,
        ∀ E₀ : Finset (Fin (A.model n).size), E₀ ⊆ D →
          2 * E₀.card ≤ D.card →
            gamma * (E₀.card : ℝ) ≤
              (SoficGroups.boundary
                (fun i : ↥S =>
                  (A.model n).action
                    (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                      i)) E₀ : ℝ) := by
    exact hexpand
  have htransported :=
    SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_half_expansion
      A S Q gamma hexpand'
  refine ⟨S, hsymmetric, hgenerates, Q, gamma, N, r, C,
    hone, hgamma,
    hsource', hr, hCpart, hCnonempty, ?_, ?_, ?_, hCgrowth⟩
  · intro n D hDC hhalf
    change gamma * (D.card : ℝ) ≤
      (SoficGroups.boundary
        (fun i : ↥S =>
          (A.model (n + N)).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
            (A.model (n + N)).action
              (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion i) *
            ((A.model (n + N)).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
        D : ℝ)
    exact htransported (n + N) (C n) (hCpart n) D hDC hhalf
  · simpa only [sigma] using hCboundary
  · simpa only [P, E, sourceTransportedPartition,
      sourceCompressionPermutation, sourceSelectedProductRadiusLabels,
      SoficGroups.SourceGuardedCanonicalSelection.guardedCanonicalProductRadiusBad,
      sourceSelectedRadiusBad] using hCbad
end SoficGroups.KunLiteralSourceSelectedComponents
