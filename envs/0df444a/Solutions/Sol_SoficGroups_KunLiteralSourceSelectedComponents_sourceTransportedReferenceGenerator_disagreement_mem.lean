-- Prove2me | solution 1 for SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerator_disagreement_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/3183bea4-f9a9-4da1-80c1-8eb66bb9ad12

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_u_conjugated_product_generator

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents
namespace SoficGroups.KunLiteralSourceSelectedComponents
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (n : ℕ) (i : ↥SΓ) (x : Fin (A.model n).size)
    (h : sourceTransportedReferenceGenerators A SΓ n i x ≠
      ((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation A).model n).action
        (SoficGroups.SourceProductThroughAlpha.sourceCompressionUAlphaEquiv
          (i : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode),
          1) x) :
    x ∈ sourceGeneratorFamilyConjugacyBad A SΓ n := by
  classical
  unfold sourceGeneratorFamilyConjugacyBad
  apply Finset.mem_biUnion.mpr
  refine ⟨(i : SoficGroups.prefixElementaryGroup
    SoficGroups.alphaPrefixCode), i.property, ?_⟩
  unfold sourceConjugacyDisagreementBad
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ x, ?_⟩
  change
    (A.model n).action
      (SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
        SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
          (i : SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode) *
        SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement⁻¹) x ≠
      sourceTransportedReferenceGenerators A SΓ n i x
  rw [← SoficGroups.SourceProductThroughAlpha.source_u_conjugated_product_generator]
  exact Ne.symm h
end SoficGroups.KunLiteralSourceSelectedComponents
