-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.source_compressed_local_product_ball_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/6a93f549-cd92-44e3-b941-4221ac24b1fe

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_compressed_local_product_word_crossing_density_tendsto_zero

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
    (I : ℕ → Finset
      (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode ×
        SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
            SoficGroups.ThompsonPrefixLocal.sourceLocalWord))
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((∑ z ∈ I k,
          (SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action
              (SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
                z))).card : ℕ) : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n =>
          ∑ z ∈ I k,
            ((SoficGroups.partitionWordCrossing (Q n)
              ((A.model n).action
                (SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
                  z))).card : ℝ) /
                (A.model n).size)
        atTop (𝓝 0) := by
    simpa using
      tendsto_finsetSum (I k) (fun z _ =>
        source_compressed_local_product_word_crossing_density_tendsto_zero
          A SΓ hsymmetric hgenerates Q hboundary z)
  simpa only [Nat.cast_sum, Finset.sum_div] using hsum
end SoficGroups.SourceProductThroughAlpha
