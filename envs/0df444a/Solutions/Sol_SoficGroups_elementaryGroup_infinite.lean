-- Prove2me | solution 1 for SoficGroups.elementaryGroup_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/280bb6a3-da73-48b7-9470-dcf87cf32204

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_elementaryUnit_injective

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
namespace SoficGroups
theorem _root_.solution [Infinite R] (i j : ι) (h : i ≠ j) :
    Infinite (elementaryGroup ι R) := by
  apply Infinite.of_injective
    (fun a : R => (⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ :
      elementaryGroup ι R))
  intro a b hab
  exact elementaryUnit_injective i j h (congrArg Subtype.val hab)
end SoficGroups
