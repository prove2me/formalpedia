-- Prove2me | solution 1 for SoficGroups.finpartition_dominant_matching_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/ada2072a-549d-4dae-b36e-536d849ec126

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_disjoint_dominant_intersections_false

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
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hmajor : ∀ C ∈ R, (D C).card < 2 * (C ∩ D C).card) :
    Set.InjOn D (R : Set (Finset V)) := by
  intro C hC E hE heq
  have hCR : C ∈ R := hC
  have hER : E ∈ R := hE
  by_contra hne
  exact disjoint_dominant_intersections_false C E (D C)
    (P.disjoint (hR hCR) (hR hER) hne)
    (hmajor C hCR)
    (by simpa [heq] using hmajor E hER)
end SoficGroups
