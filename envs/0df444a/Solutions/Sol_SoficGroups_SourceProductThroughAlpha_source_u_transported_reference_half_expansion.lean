-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_half_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/b7975b67-58da-44b8-915d-78842f93638e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transportedUnivFinpartition_half_expansion

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (QΓ : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (gamma : ℝ)
    (hexpand : ∀ n, ∀ C ∈ (QΓ n).parts,
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) E : ℝ)) :
    ∀ n, ∀ C ∈
      (SoficGroups.transportedUnivFinpartition
        (QΓ n)
        ((A.model n).action
          SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                    SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
                  (A.model n).action
                    (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                      i) *
                    ((A.model n).action
                      SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
              E : ℝ) := by
  intro n
  exact
    SoficGroups.KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
      (QΓ n)
      (fun i : ↥SΓ =>
        (A.model n).action
          (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion i))
      ((A.model n).action
        SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)
      gamma (hexpand n)
end SoficGroups.SourceProductThroughAlpha
