-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.secondFactor_mem_sourceProductRadiusLabels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/e06819bb-7547-4eab-88b4-b6b9d66bc6e5

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {j : J}
    (hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F) :
    ((1 : K), j) ∈ sourceProductRadiusLabels S F k := by
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
