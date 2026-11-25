-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.half_hexagon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:36.326798+00:00
-- url     : https://prove2.me/submissions/a3bba804-6a73-45d5-8a50-bf1eabdcbefb

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_ker_Tmap_g
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_exists_rel
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_exists_delta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {M : Type*} [AddCommGroup M]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range ∧
      δ.ker = (Tmap g h.gD h.gN).range ∧ (Tmap f h.fN h.fD).ker = δ.range := by
  obtain ⟨δ, hδ⟩ := exists_delta h
  refine ⟨δ, ker_Tmap_g h, ?_, ?_⟩
  · ext x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    constructor
    · intro hx
      obtain ⟨a, b, hb, ha⟩ := exists_rel h c
      rw [AddMonoidHom.mem_ker, hδ c a ⟨b, hb, ha⟩, mk_eq_zero_iff] at hx
      obtain ⟨a', ha'⟩ := hx
      have hk : DB (b - f a') = 0 := by rw [map_sub, ← h.fD, ha', ha, sub_self]
      refine ⟨QuotientAddGroup.mk ⟨b - f a', hk⟩, ?_⟩
      rw [Tmap_mk]
      congr 1
      apply Subtype.ext
      rw [kerMap_coe]
      change g (b - f a') = c
      rw [map_sub, (h.exact _).2 ⟨a', rfl⟩, sub_zero, hb]
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [Tmap_mk] at hy
      have hb : DB (b : B) = 0 := b.2
      rw [AddMonoidHom.mem_ker, ← hy, hδ _ 0 ⟨b, rfl, by rw [hb]; exact map_zero f⟩]
      rfl
  · ext y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]
    constructor
    · rintro ⟨b, hb⟩
      have hc : DC (g b) = 0 := by rw [← h.gD, hb]; exact (h.exact _).2 ⟨a, rfl⟩
      exact ⟨QuotientAddGroup.mk ⟨g b, hc⟩, hδ _ a ⟨b, rfl, hb.symm⟩⟩
    · rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨a', b, hb, ha'⟩ := exists_rel h c
      rw [hδ c a' ⟨b, hb, ha'⟩, mk_eq_mk_iff] at hx
      obtain ⟨a'', ha''⟩ := hx
      refine ⟨b - f a'', ?_⟩
      rw [map_sub, ← h.fD, ha'', map_sub, ha']
      abel
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
