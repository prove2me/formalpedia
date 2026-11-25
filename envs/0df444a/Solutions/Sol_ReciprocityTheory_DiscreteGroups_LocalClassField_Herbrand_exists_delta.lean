-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.exists_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:03.834523+00:00
-- url     : https://prove2.me/submissions/579d31a1-a9c2-4325-b3f7-8072b31ea9d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_exists_rel
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_rel_unique

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
theorem _root_.solution (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a →
      δ (QuotientAddGroup.mk c) = QuotientAddGroup.mk a := by
  classical
  let δ0 : DC.ker →+ T NA DA := AddMonoidHom.mk'
    (fun c => QuotientAddGroup.mk (Classical.choose (exists_rel h c))) (fun c c' => by
      rw [← QuotientAddGroup.mk_add]
      refine rel_unique h (Classical.choose_spec (exists_rel h (c + c'))) ?_
      obtain ⟨b, hb, ha⟩ := Classical.choose_spec (exists_rel h c)
      obtain ⟨b', hb', ha'⟩ := Classical.choose_spec (exists_rel h c')
      exact ⟨b + b', by rw [map_add, hb, hb']; rfl, by
        rw [map_add, ← ha, ← ha', ← map_add]; rfl⟩)
  have hδ0 : ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a → δ0 c = QuotientAddGroup.mk a :=
    fun c a hca => rel_unique h (Classical.choose_spec (exists_rel h c)) hca
  refine ⟨QuotientAddGroup.lift _ δ0 ?_, fun c a hca => ?_⟩
  · intro c hc
    rw [AddSubgroup.mem_addSubgroupOf] at hc
    obtain ⟨c0, hc0⟩ := hc
    obtain ⟨b0, rfl⟩ := h.surj c0
    rw [AddMonoidHom.mem_ker, hδ0 c 0 ⟨NB b0, by rw [h.gN, hc0], by rw [h.DN]; exact map_zero f⟩]
    rfl
  · rw [QuotientAddGroup.lift_mk]
    exact hδ0 c a hca
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
