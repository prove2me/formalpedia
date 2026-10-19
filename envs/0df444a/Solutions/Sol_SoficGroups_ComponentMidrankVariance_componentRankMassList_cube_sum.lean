-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.componentRankMassList_cube_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/3768e3f5-dc35-4fe1-8aeb-72d4aab54ee7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_map_sort_eq

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
    (C : Finset V) (b : V → ℤ) :
    ((SoficGroups.componentRankMassList C b).map fun p => p ^ 3).sum =
      ∑ j ∈ C.image b, SoficGroups.componentRankMass C b j ^ 3 := by
  unfold SoficGroups.componentRankMassList
  simp only [List.map_map]
  exact SoficGroups.sum_map_sort_eq (C.image b)
    (fun j => SoficGroups.componentRankMass C b j ^ 3)
end SoficGroups.ComponentMidrankVariance
