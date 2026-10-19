-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.source_compressed_local_product_word_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/3f611d5d-7294-442c-9a1a-b311227dca67

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_source_alpha_word_crossing_density_tendsto_zero
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_sourceCompressedLocalProductEmbedding_factors_through_alpha

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
universe v
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution
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
    (z : SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode ×
        SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
            SoficGroups.ThompsonPrefixLocal.sourceLocalWord) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action
            (SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
              z))).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  have hfactor :
      SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
          (sourceCompressedLocalProductToAlpha z) =
        SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
          z := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        sourceCompressedLocalProductEmbedding_factors_through_alpha z
  have hword :=
    SoficGroups.SourceGeneratedWordCrossing.source_alpha_word_crossing_density_tendsto_zero
        A SΓ hsymmetric hgenerates Q hboundary
          (sourceCompressedLocalProductToAlpha z)
  simpa only [hfactor] using hword
end SoficGroups.SourceProductThroughAlpha
