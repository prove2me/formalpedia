-- Prove2me | solution 1 for SoficGroups.matchedCore_subset_retainedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/d3ea3106-3fdc-46f7-8820-11b6540a98c7

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
    {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) (D : Finset V → Finset V) :
    matchedCore R D ⊆ matchedRetainedSupport R := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr
    ⟨C, hC, by simpa using (Finset.mem_inter.mp hxC).1⟩
end SoficGroups
