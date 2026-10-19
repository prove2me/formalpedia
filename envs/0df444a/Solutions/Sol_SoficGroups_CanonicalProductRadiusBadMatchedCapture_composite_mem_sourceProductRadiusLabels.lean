-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.composite_mem_sourceProductRadiusLabels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/84468cca-f2f5-4d6d-8486-90a18fb4d006

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
    {a : K} (ha : a ∈ S)
    {j : J}
    (hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F) :
    (a, j) ∈ sourceProductRadiusLabels S F k := by
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨a, ha, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
