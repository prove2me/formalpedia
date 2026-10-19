-- Prove2me | solution 1 for SoficGroups.KunLiteralNineSourceFiniteModels.source_ambient_nonempty_expandingCentralizerFiniteModel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/9c50e78c-7b98-4004-b793-49bf56faa585

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_sourceCompressedGeneratingFinset_one_mem
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_exists_sourceCompressedKazhdanPair_with_same_generators
import Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_exists_source_selected_components
import Theorems.Thm_SoficGroups_KunGuardedCanonicalMatchedDensity_canonical_matched_density_of_guarded
import Theorems.Thm_SoficGroups_KunActualCanonicalSelectedFiniteModelComposition_nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
import Theorems.Thm_SoficGroups_KunActualSourceSelectedCompletedGeneratorExpansion_exists_vanishing_completed_first_factor_additive_expansion_of_selected_source

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralNineSourceFiniteModels
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise
namespace SoficGroups.KunLiteralNineSourceFiniteModels
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord)) :
    Nonempty
      (SoficGroups.ExpandingCentralizerFiniteModel
        (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
          SoficGroups.ThompsonPrefixLocal.sourceLocalWord) F) := by
  classical
  obtain ⟨S, hsymmetric, hgenerates, Q, gamma, N, r, C,
      hone, hgamma, _hsource, hr, hC, hCnonempty,
      hexpand, hboundary, hguarded, hlarge⟩ :=
    SoficGroups.KunLiteralSourceSelectedComponents.exists_source_selected_components
      A F
  let K : Type :=
    SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode
  let J : Type :=
    SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
      SoficGroups.ThompsonPrefixLocal.sourceLocalWord
  let AP : SoficGroups.SoficApproximation (K × J) :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
      A
  let SK : Finset K :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset S
  have hSKone : 1 ∈ SK :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_one_mem
      S hone
  have hSKsymmetric : ∀ k ∈ SK, k⁻¹ ∈ SK :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
      S hsymmetric
  have hSKgenerates : Subgroup.closure (SK : Set K) = ⊤ :=
    SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
      S hgenerates
  have hpair : ∃ P : SoficGroups.KazhdanPair.{0, 0} K,
      P.generators = SK :=
    SoficGroups.SourceProductThroughAlpha.exists_sourceCompressedKazhdanPair_with_same_generators
      S hsymmetric hgenerates
  obtain ⟨PK, hPK⟩ := hpair
  have hcover : PK.generators ⊆ SK := by
    rw [hPK]
  let ν : ℕ → ℕ := fun n => n + N
  let QK : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (AP.model (ν n)).size)) :=
    fun n =>
      SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedPartition
        A Q (n + N)
  have hCK (n : ℕ) : C n ∈ (QK n).parts := hC n
  have hbad_eq (n : ℕ) :
      SoficGroups.KunLiteralSourceSelectedComponents.sourceSelectedRadiusBad
        A S hsymmetric hgenerates F (n + N) (r n) =
        canonicalProductRadiusBad
          AP SK hSKsymmetric hSKgenerates F (ν n) (r n) ∪
        SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
          A S (n + N) := by
    rfl
  have hlabel_eq (n : ℕ) :
      SoficGroups.KunLiteralSourceSelectedComponents.sourceSelectedProductRadiusLabels
        S F (r n) =
      sourceProductRadiusLabels SK F (r n) := by
    rfl
  have hguarded' :
      Tendsto
        (fun n =>
          (((C n ∩ SoficGroups.matchedRadiusBad
            (QK n)
            (sourceProductRadiusLabels SK F (r n))
            ((AP.model (ν n)).action)
            (canonicalProductRadiusBad
              AP SK hSKsymmetric hSKgenerates F (ν n) (r n) ∪
              SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
                A S (n + N))).card : ℝ) /
              (C n).card))
        atTop (𝓝 0) := by
    have hguarded_eq := hguarded
    simp_rw [hbad_eq, hlabel_eq] at hguarded_eq
    convert hguarded_eq using 1
    funext n
    simp only [QK, AP, ν]
    congr 2
  have hcanonical :
      Tendsto
        (fun n =>
          (((C n ∩ SoficGroups.matchedRadiusBad
            (QK n)
            (sourceProductRadiusLabels SK F (r n))
            ((AP.model (ν n)).action)
            (canonicalProductRadiusBad
              AP SK hSKsymmetric hSKgenerates F (ν n) (r n))).card : ℝ) /
              (C n).card))
        atTop (𝓝 0) := by
    exact SoficGroups.KunGuardedCanonicalMatchedDensity.canonical_matched_density_of_guarded
      (fun n => Fin (AP.model (ν n)).size)
      (fun n => (Finset.univ : Finset (Fin (AP.model (ν n)).size)))
      QK
      (fun n => sourceProductRadiusLabels SK F (r n))
      (fun n => (AP.model (ν n)).action)
      (fun n => canonicalProductRadiusBad
        AP SK hSKsymmetric hSKgenerates F (ν n) (r n))
      (fun n =>
        SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
          A S (n + N))
      C hguarded'
  obtain ⟨a, _ha_nonnegative, ha, hadd⟩ :=
    SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion.exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
      A S hsymmetric hgenerates Q F N r C gamma
      hCnonempty hexpand hboundary hguarded
  exact SoficGroups.KunActualCanonicalSelectedFiniteModelComposition.nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
    AP PK SK hSKone hcover hSKsymmetric hSKgenerates F
    ν QK C hCK r hr hcanonical hlarge gamma hgamma a ha hadd
end SoficGroups.KunLiteralNineSourceFiniteModels
