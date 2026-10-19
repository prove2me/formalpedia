-- Prove2me | solution 1 for SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.sourceAmbientGeneratedWord_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/097cb2c3-254a-4dcb-bd33-b1047bbb6122

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_fixed_generated_word_crossing_density_tendsto_zero

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
          ((A.model n).action g)).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by
  simpa only [MonoidHom.id_apply] using
    SoficGroups.SourceGeneratedWordCrossing.fixed_generated_word_crossing_density_tendsto_zero
        A (MonoidHom.id _) S hsymmetric hgenerates Q hboundary g
end SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
