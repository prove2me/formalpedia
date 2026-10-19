-- Prove2me | solution 1 for SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion.exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/1144dd80-818b-41cb-8525-07297a5b3b65

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualFirstStageReferenceExpansion_exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_boundary_sourceCompressedGeneratorSubtypeEquiv
import Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_sourceTransportedReferenceGenerator_disagreement_mem

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode)) = ⊤)
    (Q : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord))
    (N : ℕ) (r : ℕ → ℕ)
    (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size))
    (gamma : ℝ)
    (hC : ∀ n, (C n).Nonempty)
    (hexpand : ∀ n, ∀ D : Finset (Fin (A.model (n + N)).size),
      D ⊆ C n → 2 * D.card ≤ (C n).card →
        gamma * (D.card : ℝ) ≤
          (SoficGroups.boundary
            (SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
              A S (n + N)) D : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
            A S (n + N)) (C n) : ℝ) / (C n).card)
      atTop (nhds 0))
    (hguarded : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedPartition
            A Q (n + N))
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceSelectedProductRadiusLabels
            S F (r n))
          (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
            A).model (n + N)).action)
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceSelectedRadiusBad
            A S hsymmetric hgenerates F (n + N) (r n))).card : ℝ) /
              (C n).card))
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset
        {x : Fin (A.model (n + N)).size // x ∈ C n},
        gamma * min (E.card : ℝ)
          ((Fintype.card
            {x : Fin (A.model (n + N)).size // x ∈ C n} : ℝ) -
              E.card) -
          a n * Fintype.card
            {x : Fin (A.model (n + N)).size // x ∈ C n} ≤
            (SoficGroups.boundary
              (fun i :
                ↥(SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset
                  S) =>
                SoficGroups.MatchedComponentCompletion.completedRestriction
                  (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
                    A).model (n + N)).action
                    ((i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaZeroPrefixCode), 1))
                  (C n)) E : ℝ) := by
  classical
  have hbad_density : Tendsto
      (fun n =>
        (((C n ∩
          SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
            A S (n + N)).card : ℝ) / (C n).card))
      atTop (nhds 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hguarded
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (by
      intro x hx
      obtain ⟨hxC, hxE⟩ := Finset.mem_inter.mp hx
      apply Finset.mem_inter.mpr
      refine ⟨hxC, ?_⟩
      unfold SoficGroups.matchedRadiusBad
      apply Finset.mem_union_left
      change x ∈
        SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad
          (SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A)
          (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset S)
          (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_inv_mem
            S hsymmetric)
          (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset_closure
            S hgenerates)
          F (n + N) (r n) ∪
          SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
            A S (n + N)
      exact Finset.mem_union_right _ hxE)
  obtain ⟨a, ha_nonnegative, ha_zero, ha_expand⟩ :=
    SoficGroups.KunActualFirstStageReferenceExpansion.exists_vanishing_completedRestriction_additive_expansion_of_selected_bad
      (fun n => Fin (A.model (n + N)).size)
      (↥S) C
      (fun n =>
        SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad
          A S (n + N))
      hC
      (fun n =>
        SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
          A S (n + N))
      (fun n (i : ↥S) =>
        ((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
          A).model (n + N)).action
            (SoficGroups.SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
              (i : SoficGroups.prefixElementaryGroup
                SoficGroups.alphaPrefixCode), 1))
      gamma hexpand
      (fun n i x _hx hdis =>
        SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerator_disagreement_mem
          A S (n + N) i x hdis)
      hboundary hbad_density
  refine ⟨a, ha_nonnegative, ha_zero, ?_⟩
  intro n E
  have h := ha_expand n E
  have hreindex :
      SoficGroups.boundary
        (fun i : ↥S =>
          SoficGroups.MatchedComponentCompletion.completedRestriction
            (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action
              (SoficGroups.SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.alphaPrefixCode), 1))
            (C n)) E =
        SoficGroups.boundary
          (fun i :
            ↥(SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset
              S) =>
            SoficGroups.MatchedComponentCompletion.completedRestriction
              (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
                A).model (n + N)).action
                ((i : SoficGroups.prefixElementaryGroup
                  SoficGroups.alphaZeroPrefixCode), 1))
              (C n)) E := by
    exact
      SoficGroups.SourceProductThroughAlpha.boundary_sourceCompressedGeneratorSubtypeEquiv
        S
        (fun i :
          ↥(SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset
            S) =>
          SoficGroups.MatchedComponentCompletion.completedRestriction
            (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action
              ((i : SoficGroups.prefixElementaryGroup
                SoficGroups.alphaZeroPrefixCode), 1))
            (C n))
        E
  exact h.trans_eq (congrArg (fun t : ℕ => (t : ℝ)) hreindex)
end SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion
