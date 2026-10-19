-- Prove2me | solution 1 for SoficGroups.componentRankMassList_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/2c7f24e2-3087-49bc-994f-6a489f74d2f6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_componentRankMass
import Theorems.Thm_SoficGroups_sum_map_sort_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (componentRankMassList C b).sum = 1 := by
  unfold componentRankMassList
  rw [sum_map_sort_eq]
  exact sum_componentRankMass C b hC
end SoficGroups
