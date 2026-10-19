-- Prove2me | solution 1 for SoficGroups.SourceGeneratedWordCrossing.source_alpha_word_crossing_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/d09f5004-de85-448d-bbdd-39fd80be0ac7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_fixed_generated_word_crossing_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceGeneratedWordCrossing
theorem _root_.solution
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) = ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action (sourceAlphaInclusion i)) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0))
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action (sourceAlphaInclusion g))).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) :=
  fixed_generated_word_crossing_density_tendsto_zero
    A sourceAlphaInclusion S hsymmetric hgenerates Q hboundary g
end SoficGroups.SourceGeneratedWordCrossing
