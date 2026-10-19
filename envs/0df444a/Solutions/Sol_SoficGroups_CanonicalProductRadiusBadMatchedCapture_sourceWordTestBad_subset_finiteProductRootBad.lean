-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceWordTestBad_subset_finiteProductRootBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/c3102429-4084-468b-a596-f2a2227e01be

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_mem_productTrackedTable
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_multiplicative
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_separated
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_secondFactor_mem_sourceProductRadiusLabels
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_generator_mem_sourceProductRadiusLabels

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
    (S : Finset K) (F : Finset J) (n k : ℕ) :
    sourceWordTestBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F ⊆
        finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k) := by
  classical
  intro x hx
  by_contra hxroot
  simp only [sourceWordTestBad, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx
  rcases hx with (hcomm | hmul) | hsep
  · obtain ⟨i, j, hj, hfailure⟩ := hcomm
    have hfirst :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hj)
        (generator_mem_sourceProductRadiusLabels
          S F k i.property)
        hxroot
    have hsecond :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (generator_mem_sourceProductRadiusLabels
          S F k i.property)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hj)
        hxroot
    apply hfailure
    calc
      (A.model n).action (1, j)
          ((A.model n).action ((i : K), 1) x) =
        (A.model n).action ((1, j) * ((i : K), 1)) x := by
          simpa [Equiv.Perm.mul_apply] using hfirst.symm
      _ = (A.model n).action
          (((i : K), 1) * (1, j)) x := by simp
      _ = (A.model n).action ((i : K), 1)
          ((A.model n).action (1, j) x) := by
          simpa [Equiv.Perm.mul_apply] using hsecond
  · obtain ⟨j, hj, l, hl, hfailure⟩ := hmul
    have hjT :=
      SoficGroups.CompressionCriterion.mem_productTrackedTable hj
    have hlT :=
      SoficGroups.CompressionCriterion.mem_productTrackedTable hl
    have hproduct :=
      finiteRootBad_multiplicative
        (A.model n) (sourceProductRadiusLabels S F k)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hjT)
        (secondFactor_mem_sourceProductRadiusLabels
          S F k hlT)
        hxroot
    apply hfailure
    simpa [Equiv.Perm.mul_apply] using hproduct
  · obtain ⟨j, hj, l, hl, hne, heq⟩ := hsep
    have hjT :=
      SoficGroups.CompressionCriterion.mem_productTrackedTable hj
    have hlT :=
      SoficGroups.CompressionCriterion.mem_productTrackedTable hl
    have hne' : ((1 : K), j) ≠ ((1 : K), l) := by
      intro h
      exact hne (congrArg Prod.snd h)
    exact finiteRootBad_separated
      (A.model n) (sourceProductRadiusLabels S F k)
      (secondFactor_mem_sourceProductRadiusLabels S F k hjT)
      (secondFactor_mem_sourceProductRadiusLabels S F k hlT)
      hne' hxroot heq
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
