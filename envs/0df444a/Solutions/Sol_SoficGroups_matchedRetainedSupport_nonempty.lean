-- Prove2me | solution 1 for SoficGroups.matchedRetainedSupport_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/ee663e79-9270-45c7-994c-f09e990209d8

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
    (hR : R ⊆ P.parts) (hRne : R.Nonempty) :
    (matchedRetainedSupport R).Nonempty := by
  obtain ⟨C, hC⟩ := hRne
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts (hR hC)
  refine ⟨x, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨C, hC, by simpa using hx⟩
end SoficGroups
