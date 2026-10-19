-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.component_exit_mem_partitionWordCrossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/c342a036-36dd-45f8-8131-7541eb740fcf

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
    {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U)
    (C : Finset V) (hC : C ∈ P.parts)
    (p : Equiv.Perm V) {x : V}
    (hx : x ∈ C) (hout : p x ∉ C) :
    x ∈ SoficGroups.partitionWordCrossing P p := by
  have hxU : x ∈ U := P.subset hC hx
  change x ∈ U.filter fun y => p y ∉ P.part y
  apply Finset.mem_filter.mpr
  refine ⟨hxU, ?_⟩
  rwa [P.part_eq_of_mem hC hx]
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
