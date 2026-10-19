-- Prove2me | solution 1 for SoficGroups.KunActualCanonicalPrunedSourceBadDensity.pruned_sourceCompletionBad_density_tendsto_zero_of_canonical_matched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/f8af288b-de63-4f91-9c22-1eb45e6df72e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedFirstStageWordRadiusTransfer_pruned_sourceCompletionBad_density_tendsto_zero_of_matchedRadius
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_sourceCompletionBad_subset_canonical_matchedRadiusBad

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualCanonicalPrunedSourceBadDensity
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
namespace SoficGroups.KunActualCanonicalPrunedSourceBadDensity
theorem _root_.solution
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
          (C n).card))
      atTop (𝓝 0))
    (D : (n : ℕ) → Finset
      {x : Fin (A.model (ν n)).size // x ∈ C n})
    (hZ : ∀ n,
      (Finset.univ \ D n :
        Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / (C n).card)
      atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        ((sourceCompletionBad
          (fun i : ↥S =>
            completedRestriction
              ((A.model (ν n)).action ((i : K), (1 : J))) (C n))
          (fun j : J =>
            completedRestriction
              ((A.model (ν n)).action ((1 : K), j)) (C n))
          F (Finset.univ \ D n)).card : ℝ) /
            (Finset.univ \ D n :
              Finset {x : Fin (A.model (ν n)).size // x ∈ C n}).card)
      atTop (𝓝 0) := by
  apply SoficGroups.MatchedFirstStageWordRadiusTransfer.pruned_sourceCompletionBad_density_tendsto_zero_of_matchedRadius
    (fun n => Fin (A.model (ν n)).size)
    (fun n (i : ↥S) => (A.model (ν n)).action ((i : K), (1 : J)))
    (fun n (j : J) => (A.model (ν n)).action ((1 : K), j))
    F
    (fun n => (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    C Q
    (fun k => sourceProductRadiusLabels S F k)
    (fun n => (A.model (ν n)).action)
    r
    (fun n k => canonicalProductRadiusBad
      A S hsymmetric hgenerates F (ν n) k)
    D
  · intro n
    exact sourceCompletionBad_subset_canonical_matchedRadiusBad
      A S hsymmetric hgenerates F (ν n) (r n)
      (Q n) (C n) (hC n)
  · exact hmatched
  · exact hZ
  · exact hdeleted
end SoficGroups.KunActualCanonicalPrunedSourceBadDensity
