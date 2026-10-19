-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.firstFactor_mem_sourceProductRadiusLabels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/da025f3f-1dbc-44b6-8be9-ccd61a884f30

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
    {a : K} (ha : a ∈ S ^ k) :
    (a, (1 : J)) ∈ sourceProductRadiusLabels S F k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
