-- Prove2me | solution 1 for SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.sourceAmbientFiniteFamily_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/f835c484-1330-47e8-a115-a3485809c5eb

import Mathlib
import Definitions.Def_NonSoficGroup
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
    (ι : Type*) [Fintype ι]
    (g : ι →
      SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :
    Tendsto
      (fun n =>
        (∑ i : ι,
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action (g i))).card : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n =>
        ∑ i : ι,
          ((SoficGroups.partitionWordCrossing (Q n)
            ((A.model n).action (g i))).card : ℝ) /
              (A.model n).size)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset ι)
      (fun i _ => sourceAmbientGeneratedWord_crossing_density_tendsto_zero
        A S hsymmetric hgenerates Q hboundary (g i))
  simpa only [Finset.sum_div] using hsum
end SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
