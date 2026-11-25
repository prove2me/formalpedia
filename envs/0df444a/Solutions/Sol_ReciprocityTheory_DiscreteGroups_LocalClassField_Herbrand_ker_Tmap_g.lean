-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.ker_Tmap_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:40.566956+00:00
-- url     : https://prove2.me/submissions/73262220-06fe-4d5f-a824-e78ada62a220

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
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
    (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range := by
  ext x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b', rfl⟩ := h.surj c
    have h1 : g ((b : B) - NB b') = 0 := by rw [map_sub, h.gN, hc, sub_self]
    obtain ⟨a, ha⟩ := (h.exact _).1 h1
    have hb : DB (b : B) = 0 := b.2
    have haD : DA a = 0 := h.inj (by rw [h.fD, ha, map_sub, hb, h.DN, sub_zero, map_zero])
    refine ⟨QuotientAddGroup.mk ⟨a, haD⟩, ?_⟩
    rw [Tmap_mk, mk_eq_mk_iff, kerMap_coe]
    exact ⟨-b', by rw [map_neg]; change _ = f a - b; rw [ha]; abel⟩
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [Tmap_mk, mk_eq_mk_iff, kerMap_coe] at hy
    obtain ⟨b', hb'⟩ := hy
    refine ⟨- g b', ?_⟩
    have h0 : g (f a) = 0 := (h.exact _).2 ⟨a, rfl⟩
    have := congrArg g hb'
    rw [map_sub, h0, h.gN, zero_sub] at this
    rw [map_neg, this, neg_neg]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
