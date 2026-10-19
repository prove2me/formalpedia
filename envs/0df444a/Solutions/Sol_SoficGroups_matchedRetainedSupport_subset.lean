-- Prove2me | solution 1 for SoficGroups.matchedRetainedSupport_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/cb298a62-4b87-46d3-a422-5e0519a94b6e

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
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) :
    matchedRetainedSupport R ⊆ U := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact P.subset (hR hC) (by simpa using hxC)
end SoficGroups
