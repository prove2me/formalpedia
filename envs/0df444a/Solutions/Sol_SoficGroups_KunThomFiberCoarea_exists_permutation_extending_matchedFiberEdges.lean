-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.exists_permutation_extending_matchedFiberEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/0d87ca04-5378-46df-a2d6-7f88e4d54841

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [DecidableEq V] (U : Finset (V × V)) :
    ∃ p : Equiv.Perm V,
      ∀ z ∈ matchedFiberEdges U, p z.1 = z.2 := by
  classical
  let A := {z : V × V // z ∈ matchedFiberEdges U}
  let f : A → V := fun z => z.1.1
  let g : A → V := fun z => z.1.2
  have hf : Function.Injective f := by
    intro z w h
    have hz := Finset.mem_filter.mp z.property
    have hw := Finset.mem_filter.mp w.property
    have hcard :
        (U.filter fun t => t.1 = z.1.1).card ≤ 1 := by
      have heq : firstMultiplicity U z.1.1 = 1 := hz.2.1
      simpa [firstMultiplicity, firstFiber] using Nat.le_of_eq heq
    have hzmem : z.1 ∈ U.filter fun t => t.1 = z.1.1 :=
      Finset.mem_filter.mpr ⟨hz.1, rfl⟩
    have hwmem : w.1 ∈ U.filter fun t => t.1 = z.1.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨hw.1, ?_⟩
      exact h.symm
    exact Subtype.ext
      ((Finset.card_le_one_iff.mp hcard) hzmem hwmem)
  have hg : Function.Injective g := by
    intro z w h
    have hz := Finset.mem_filter.mp z.property
    have hw := Finset.mem_filter.mp w.property
    have hcard :
        (U.filter fun t => t.2 = z.1.2).card ≤ 1 := by
      have heq : secondMultiplicity U z.1.2 = 1 := hz.2.2
      simpa [secondMultiplicity, secondFiber] using Nat.le_of_eq heq
    have hzmem : z.1 ∈ U.filter fun t => t.2 = z.1.2 :=
      Finset.mem_filter.mpr ⟨hz.1, rfl⟩
    have hwmem : w.1 ∈ U.filter fun t => t.2 = z.1.2 := by
      apply Finset.mem_filter.mpr
      refine ⟨hw.1, ?_⟩
      exact h.symm
    exact Subtype.ext
      ((Finset.card_le_one_iff.mp hcard) hzmem hwmem)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨p, ?_⟩
  intro z hz
  exact hp ⟨z, hz⟩
end SoficGroups.KunThomFiberCoarea
