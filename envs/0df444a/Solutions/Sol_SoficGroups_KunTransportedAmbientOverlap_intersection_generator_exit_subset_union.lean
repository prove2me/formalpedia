-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.intersection_generator_exit_subset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/14ee5f27-eb7c-4fab-8a68-e2bf848d37ee

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (C D : Finset V) :
    ((C ∩ D).filter fun x => p x ∉ C ∩ D) ⊆
      ((C.filter fun x => p x ∉ C) ∩ D) ∪
        ((D.filter fun x => p x ∉ D) ∩ C) := by
  intro x hx
  obtain ⟨hxCD, hout⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hxCD
  by_cases hpC : p x ∈ C
  · apply Finset.mem_union_right
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hxD, ?_⟩, hxC⟩
    intro hpD
    exact hout (Finset.mem_inter.mpr ⟨hpC, hpD⟩)
  · apply Finset.mem_union_left
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨hxC, hpC⟩, hxD⟩
end SoficGroups.KunTransportedAmbientOverlap
