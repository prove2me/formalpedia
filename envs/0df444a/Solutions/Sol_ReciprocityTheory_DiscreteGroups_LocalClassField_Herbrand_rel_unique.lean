-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.rel_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:03.085726+00:00
-- url     : https://prove2.me/submissions/da003f6a-e347-4d6e-b7b5-a33abc4c2cb5

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {M : Type*} [AddCommGroup M]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (h : SES DA NA DB NB DC NC f g) {c : C} {a a' : NA.ker} (h1 : Rel DB f g c a)
    (h2 : Rel DB f g c a') : (QuotientAddGroup.mk a : T NA DA) = QuotientAddGroup.mk a' := by
  obtain ⟨b, hb, ha⟩ := h1
  obtain ⟨b', hb', ha'⟩ := h2
  rw [mk_eq_mk_iff]
  obtain ⟨x, hx⟩ := (h.exact (b - b')).1 (by rw [map_sub, hb, hb', sub_self])
  exact ⟨x, h.inj (by rw [h.fD, hx, map_sub, map_sub, ha, ha'])⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
