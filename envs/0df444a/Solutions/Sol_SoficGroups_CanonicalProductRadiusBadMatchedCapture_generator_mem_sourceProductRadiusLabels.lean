-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.generator_mem_sourceProductRadiusLabels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/723a2f4c-58f0-4464-bfa3-18612692ed23

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompressionCriterion_one_mem_productTrackedTable
import Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_composite_mem_sourceProductRadiusLabels

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
    (S : Finset K) (F : Finset J) (k : ℕ)
    {a : K} (ha : a ∈ S) :
    (a, (1 : J)) ∈ sourceProductRadiusLabels S F k :=
  composite_mem_sourceProductRadiusLabels S F k ha
    (SoficGroups.CompressionCriterion.one_mem_productTrackedTable F)
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
