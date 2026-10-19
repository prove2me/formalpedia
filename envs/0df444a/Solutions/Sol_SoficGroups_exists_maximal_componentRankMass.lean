-- Prove2me | solution 1 for SoficGroups.exists_maximal_componentRankMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/c9679eba-bee3-4b11-81f3-e5f51a4d92e4

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    ∃ j ∈ C.image b,
      ∀ k ∈ C.image b,
        componentRankMass C b k ≤ componentRankMass C b j := by
  have himage : (C.image b).Nonempty := hC.image b
  obtain ⟨j, hj, hmax⟩ :=
    Finset.exists_max_image (C.image b) (componentRankMass C b) himage
  exact ⟨j, hj, hmax⟩
end SoficGroups
