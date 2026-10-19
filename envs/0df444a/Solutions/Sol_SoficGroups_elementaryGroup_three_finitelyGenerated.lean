-- Prove2me | solution 1 for SoficGroups.elementaryGroup_three_finitelyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/64d8f68a-2f5f-40de-b5be-cda2fa212dc9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_elementaryGroup_finitelyGenerated

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
variable {R : Type*} [Ring R]
variable [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    [Algebra.FiniteType (ZMod 2) R] :
    Group.FG (elementaryGroup (Fin 3) R) :=
  elementaryGroup_finitelyGenerated 3 (by decide)
end SoficGroups
