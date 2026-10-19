-- Prove2me | solution 1 for SoficGroups.KunActualTwicePrunedFirstFactorRootBad.firstFactor_completed_mul_distance_le_canonical_matched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/66719650-047f-4ea7-891a-bf049283c7b8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_multiplicative
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtypeBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_permutationDistance_le_subtypeBad
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_firstFactor_mem_sourceProductRadiusLabels
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_component_exit_mem_partitionWordCrossing
import Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_completedRestriction_mul_of_not_mem_restrictionMultiplicationBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualTwicePrunedFirstFactorRootBad
theorem _root_.solution
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (Q : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ Q.parts)
    (a g : K)
    (ha : a ∈ S ^ k) (hg : g ∈ S ^ k)
    (hag : a * g ∈ S ^ k) :
    SoficGroups.permutationDistance
        (completedRestriction
          ((A.model n).action (a * g, (1 : J))) C)
        (completedRestriction
          ((A.model n).action (a, (1 : J))) C *
         completedRestriction
          ((A.model n).action (g, (1 : J))) C) ≤
      (C ∩ SoficGroups.matchedRadiusBad
        Q (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)).card := by
  classical
  let B := SoficGroups.matchedRadiusBad
    Q (sourceProductRadiusLabels S F k)
    ((A.model n).action)
    (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)
  calc
    SoficGroups.permutationDistance
        (completedRestriction
          ((A.model n).action (a * g, (1 : J))) C)
        (completedRestriction
          ((A.model n).action (a, (1 : J))) C *
         completedRestriction
          ((A.model n).action (g, (1 : J))) C) ≤
        (subtypeBad C B).card := by
      apply permutationDistance_le_subtypeBad C B
      intro x hx
      apply completedRestriction_mul_of_not_mem_restrictionMultiplicationBad
        ((A.model n).action (a, (1 : J)))
        ((A.model n).action (g, (1 : J)))
        ((A.model n).action (a * g, (1 : J))) C x
      intro hfailure
      have hbad := (Finset.mem_filter.mp hfailure).2
      have hnotcross (b : K) (hb : b ∈ S ^ k) :
          (x : Fin (A.model n).size) ∉
            SoficGroups.partitionWordCrossing
              Q ((A.model n).action (b, (1 : J))) := by
        intro hcross
        apply hx
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨(b, (1 : J)),
            firstFactor_mem_sourceProductRadiusLabels S F k hb,
            hcross⟩
      rcases hbad with hq | hr | hmul
      · exact hnotcross g hg
          (component_exit_mem_partitionWordCrossing
            Q C hC ((A.model n).action (g, (1 : J)))
            x.property hq)
      · exact hnotcross (a * g) hag
          (component_exit_mem_partitionWordCrossing
            Q C hC ((A.model n).action (a * g, (1 : J)))
            x.property hr)
      · have hnotroot :
            (x : Fin (A.model n).size) ∉
              finiteRootBad (A.model n)
                (sourceProductRadiusLabels S F k) := by
          intro hroot
          apply hx
          apply Finset.mem_union_left
          exact Finset.mem_union_right _ hroot
        have hroot := finiteRootBad_multiplicative
          (A.model n) (sourceProductRadiusLabels S F k)
          (firstFactor_mem_sourceProductRadiusLabels S F k ha)
          (firstFactor_mem_sourceProductRadiusLabels S F k hg)
          hnotroot
        apply hmul
        simpa [Equiv.Perm.mul_apply] using hroot
    _ = (C ∩ SoficGroups.matchedRadiusBad
        Q (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)).card :=
      card_subtypeBad C B
end SoficGroups.KunActualTwicePrunedFirstFactorRootBad
