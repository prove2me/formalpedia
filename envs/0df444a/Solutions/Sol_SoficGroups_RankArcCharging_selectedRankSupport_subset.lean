-- Prove2me | solution 1 for SoficGroups.RankArcCharging.selectedRankSupport_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/9e014f71-4a53-4a4b-8928-6609d3a6e38a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.RankArcCharging
open scoped BigOperators
namespace SoficGroups.RankArcCharging
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) :
    selectedRankSupport P b j ⊆ U := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact P.subset hC (Finset.mem_filter.mp hxC).1
end SoficGroups.RankArcCharging
