-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.source_canonical_product_radius_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/89354f39-72a8-4b05-9b39-dc6fba32b7af

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_compressed_local_product_ball_crossing_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
universe v
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution
    [DecidableEq
      (SoficGroups.prefixElementaryGroup
        SoficGroups.alphaZeroPrefixCode)]
    [DecidableEq
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
          SoficGroups.ThompsonPrefixLocal.sourceLocalWord)]
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
          SoficGroups.ThompsonPrefixLocal.sourceLocalWord))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((∑ z ∈
          SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (sourceCompressedGeneratingFinset SΓ) F k,
          (SoficGroups.partitionWordCrossing (Q n)
            (((sourceCompressedLocalProductApproximation A).model n).action
              z)).card : ℕ) : ℝ) /
            ((sourceCompressedLocalProductApproximation A).model n).size)
      atTop (𝓝 0) := by
  change
    Tendsto
      (fun n =>
        ((∑ z ∈
          SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (sourceCompressedGeneratingFinset SΓ) F k,
          (SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
              (SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
                z))).card : ℕ) : ℝ) /
              (A.model n).size)
      atTop (𝓝 0)
  exact
    source_compressed_local_product_ball_crossing_density_tendsto_zero
      A SΓ hsymmetric hgenerates Q hboundary
      (fun r =>
        SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
            (sourceCompressedGeneratingFinset SΓ) F r)
      k
end SoficGroups.SourceProductThroughAlpha
