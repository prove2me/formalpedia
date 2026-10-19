-- Prove2me | solution 1 for SoficGroups.KunLiteralSourceSelectedComponents.sourceGeneratorFamilyConjugacyBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/7907a9b4-9e31-46b4-9916-cb171af8647d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finite_union_bad_density_tendsto_zero
import Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_sourceConjugacyDisagreementBad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.SourceProductThroughAlpha
open scoped BigOperators Pointwise
namespace SoficGroups.KunLiteralSourceSelectedComponents
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) :
    Tendsto
      (fun n =>
        ((sourceGeneratorFamilyConjugacyBad A S n).card : ℝ) /
          (A.model n).size)
      atTop (nhds 0) := by
  classical
  have h := SoficGroups.finite_union_bad_density_tendsto_zero S
    (fun n => (Finset.univ : Finset (Fin (A.model n).size)))
    (fun n g => sourceConjugacyDisagreementBad A
      SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement
      (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion g) n)
    (fun g _ => by
      simpa using sourceConjugacyDisagreementBad_density_tendsto_zero A
        SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement
        (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion g))
  simpa [sourceGeneratorFamilyConjugacyBad] using h
end SoficGroups.KunLiteralSourceSelectedComponents
