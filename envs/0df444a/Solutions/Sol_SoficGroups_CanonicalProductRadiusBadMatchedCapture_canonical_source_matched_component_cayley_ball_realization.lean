-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonical_source_matched_component_cayley_ball_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/c7165c0a-4873-4455-ad29-648fb89e7fb6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono
import Theorems.Thm_SoficGroups_ChosenCayleyMatchedComponentRealization_sourceFirstFactor_injective_ball
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_firstFactor_mem_sourceProductRadiusLabels
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_component_exit_mem_partitionWordCrossing

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.CanonicalProductRadiusBadMatchedCapture
theorem _root_.solution
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K) (honeS : 1 ∈ S)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (P : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ P.parts)
    (x : Fin (A.model n).size) (hx : x ∈ C)
    (hgood : x ∉
      SoficGroups.matchedRadiusBad
        P (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k)) :
    ∃ f : K → Fin (A.model n).size,
      Set.MapsTo f
        (↑(S ^ (k / 2)) : Set K)
        (↑C : Set (Fin (A.model n).size)) ∧
      Set.InjOn f (↑(S ^ (k / 2)) : Set K) := by
  have hxsource :
      x ∉ sourceFirstFactorCayleyRadiusBad
        A S hsymmetric hgenerates n k := by
    intro hbad
    apply hgood
    apply Finset.mem_union_left
    exact Finset.mem_union_left _ hbad
  have hroot :=
    sourceFirstFactor_injective_ball
      A S hsymmetric hgenerates n k hxsource
  refine ⟨fun a => (A.model n).action (a, 1) x, ?_, ?_⟩
  · intro a ha
    have hak : a ∈ S ^ k :=
      Finset.pow_subset_pow_right honeS
        (Nat.div_le_self k 2) ha
    have halabel :=
      firstFactor_mem_sourceProductRadiusLabels S F k hak
    have hnotcross :
        x ∉ SoficGroups.partitionWordCrossing
          P ((A.model n).action (a, 1)) := by
      intro hcross
      apply hgood
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨(a, 1), halabel, hcross⟩
    have himage : (A.model n).action (a, 1) x ∈ C := by
      by_contra hout
      apply hnotcross
      exact component_exit_mem_partitionWordCrossing
        P C hC _ hx hout
    exact himage
  · apply hroot.mono
    intro a ha
    exact Finset.pow_subset_pow_right honeS
      (Nat.div_le_self k 2) ha
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
