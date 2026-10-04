-- Prove2me | solution 1 for TheoryOfGames.Acyclic.partialOrdering_conditionG_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:01:14.952491+00:00
-- url     : https://prove2.me/submissions/43e9b4d5-18b0-4356-98a7-6eff86902d7c

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_PartialOrdering

set_option autoImplicit false

open TheoryOfGames.Acyclic in
theorem solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hS : IsPartialOrdering D S) (hD : D.Finite) :
    ConditionG D S := by
  intro y hy hnm
  obtain ⟨hirr, htr⟩ := hS
  -- y is not a maximum, so some z ∈ D dominates y
  have hT : ({x | x ∈ D ∧ S x y} : Set α).Nonempty := by
    by_contra hne
    apply hnm
    refine ⟨hy, fun z hz hzy => hne ⟨z, hz, hzy⟩⟩
  have hTfin : ({x | x ∈ D ∧ S x y} : Set α).Finite := hD.subset (fun x hx => hx.1)
  obtain ⟨x, ⟨hxD, hxy⟩, hmin⟩ := Set.exists_min_image _
    (fun x => ({w | w ∈ D ∧ S w x} : Set α).ncard) hTfin hT
  refine ⟨x, ⟨hxD, fun w hwD hwx => ?_⟩, hxy⟩
  have hwy : S w y := htr w hwD x hxD y hy hwx hxy
  have hle := hmin w ⟨hwD, hwy⟩
  have hsub : ({u | u ∈ D ∧ S u w} : Set α) ⊂ {u | u ∈ D ∧ S u x} := by
    refine ⟨fun u hu => ⟨hu.1, htr u hu.1 w hwD x hxD hu.2 hwx⟩, fun h => ?_⟩
    have := h ⟨hwD, hwx⟩
    exact (hirr w hwD w hwD).1 ⟨rfl, this.2⟩
  have hlt := Set.ncard_lt_ncard hsub (hD.subset (fun u hu => hu.1))
  exact absurd hle (not_le.mpr hlt)
