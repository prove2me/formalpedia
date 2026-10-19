-- Prove2me | solution 1 for SoficGroups.componentRankMassList_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/8a64581b-c7e7-4c8d-8bc9-5f13cd779148

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ)
    (hmax : ∀ k ∈ C.image b,
      componentRankMass C b k ≤ componentRankMass C b j) :
    ∀ p ∈ componentRankMassList C b,
      p ≤ componentRankMass C b j := by
  intro p hp
  unfold componentRankMassList at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  exact hmax k (((C.image b).mem_sort (· ≤ ·)).mp hk)
end SoficGroups
