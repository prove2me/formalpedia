-- Prove2me | solution 1 for SoficGroups.componentRankMassList_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/236e7bf8-b78b-4628-8c18-32ab26dca6e4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_componentRankMass_nonneg

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    (C : Finset V) (b : V → ℤ) :
    ∀ p ∈ componentRankMassList C b, 0 ≤ p := by
  intro p hp
  unfold componentRankMassList at hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact componentRankMass_nonneg C b j
end SoficGroups
