-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.componentVertexMidrank_eq_ordered_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/722b0bbf-0409-4f08-9bfa-d2f9928bd490

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_componentVertexMidrank_eq_sum_componentRankMass

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators
namespace SoficGroups.ComponentMidrankVariance
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    SoficGroups.componentVertexMidrank C b x =
      lowerRankWeight (C.image b) (SoficGroups.componentRankMass C b) (b x) +
        SoficGroups.componentRankMass C b (b x) / 2 := by
  simpa only [lowerRankWeight] using
    SoficGroups.componentVertexMidrank_eq_sum_componentRankMass C b x
end SoficGroups.ComponentMidrankVariance
