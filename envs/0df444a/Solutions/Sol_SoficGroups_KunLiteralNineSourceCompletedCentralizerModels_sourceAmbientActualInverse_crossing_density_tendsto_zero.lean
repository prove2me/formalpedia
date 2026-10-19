-- Prove2me | solution 1 for SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.sourceAmbientActualInverse_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/10042d0c-cb0f-4bfd-b667-404aa1247f0f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_crossing_density_tendsto_zero_of_normalizedHamming
import Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sofic_action_inverse_normalizedHamming_tendsto_zero
import Theorems.Thm_SoficGroups_KunCommonRankArcInvariance_sofic_action_inverse_normalizedHamming_tendsto_zero
import Theorems.Thm_SoficGroups_KunLiteralNineSourceCompletedCentralizerModels_sourceAmbientGeneratedWord_crossing_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (g : SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          (((A.model n).action g)⁻¹)).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  have hlabel :=
    sourceAmbientGeneratedWord_crossing_density_tendsto_zero
      A S hsymmetric hgenerates Q hboundary (g⁻¹)
  have hinverse :=
    SoficGroups.KunCommonRankArcInvariance.sofic_action_inverse_normalizedHamming_tendsto_zero
      A g
  simpa only [Fintype.card_fin] using
    SoficGroups.SourceGeneratedWordCrossing.crossing_density_tendsto_zero_of_normalizedHamming
        Q (fun n => ((A.model n).action g)⁻¹)
          (fun n => (A.model n).action (g⁻¹))
          (by simpa only [Fintype.card_fin] using hlabel)
          hinverse
end SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
