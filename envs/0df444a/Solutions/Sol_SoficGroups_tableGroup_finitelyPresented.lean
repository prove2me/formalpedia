-- Prove2me | solution 1 for SoficGroups.tableGroup_finitelyPresented
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/249d0f2b-18f2-451b-a568-88fa8b4d6168

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    Group.IsFinitelyPresented (tableGroup F h₁) :=
  inferInstance
end SoficGroups
