-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceCompletionBad_subset_canonical_matchedRadiusBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/ec7d0364-0289-40a2-a832-299da3101909

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_multiplicative
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_sourceCompletionBad_subset
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_sourceCompletionBad_subset_exit_union_wordBad
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_secondFactor_mem_sourceProductRadiusLabels
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_composite_mem_sourceProductRadiusLabels
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_generator_mem_sourceProductRadiusLabels
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_sourceWordTestBad_subset_finiteProductRootBad
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
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (P : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ P.parts) :
    sourceCompletionBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C ⊆
      C ∩ SoficGroups.matchedRadiusBad
        P (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k) := by
  classical
  intro x hx
  have hxC : x ∈ C :=
    sourceCompletionBad_subset
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C hx
  refine Finset.mem_inter.mpr ⟨hxC, ?_⟩
  by_contra hnot
  have hnotbad :
      x ∉ canonicalProductRadiusBad
        A S hsymmetric hgenerates F n k := by
    intro hbad
    apply hnot
    exact Finset.mem_union_left _ hbad
  have hroot :
      x ∉ finiteRootBad (A.model n)
        (sourceProductRadiusLabels S F k) := by
    intro hbad
    exact hnotbad (Finset.mem_union_right _ hbad)
  have hnotcross :
      ∀ q ∈ sourceProductRadiusLabels S F k,
        x ∉ SoficGroups.partitionWordCrossing
          P ((A.model n).action q) := by
    intro q hq hcross
    apply hnot
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨q, hq, hcross⟩
  have hcovered :=
    sourceCompletionBad_subset_exit_union_wordBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C hx
  simp only [Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and] at hcovered
  rcases hcovered with ((hgen | hfactor) | hcomposite) | hword
  · obtain ⟨i, hx', hout⟩ := hgen
    apply hnotcross
      ((i : K), 1)
      (generator_mem_sourceProductRadiusLabels
        S F k i.property)
    exact component_exit_mem_partitionWordCrossing
      P C hC _ hx' hout
  · obtain ⟨j, hj, hx', hout⟩ := hfactor
    apply hnotcross
      ((1 : K), j)
      (secondFactor_mem_sourceProductRadiusLabels S F k hj)
    exact component_exit_mem_partitionWordCrossing
      P C hC _ hx' hout
  · obtain ⟨i, j, hj, hx', hout⟩ := hcomposite
    have hpair :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (secondFactor_mem_sourceProductRadiusLabels S F k hj)
        (generator_mem_sourceProductRadiusLabels
          S F k i.property)
        hroot
    have hvalue :
        (A.model n).action ((i : K), j) x =
          (A.model n).action (1, j)
            ((A.model n).action ((i : K), 1) x) := by
      simpa [Equiv.Perm.mul_apply] using hpair
    apply hnotcross
      ((i : K), j)
      (composite_mem_sourceProductRadiusLabels
        S F k i.property hj)
    apply component_exit_mem_partitionWordCrossing
      P C hC _ hx'
    rw [hvalue]
    exact hout
  · apply hroot
    exact sourceWordTestBad_subset_finiteProductRootBad
      A S F n k hword
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
