-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.q_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:37.884917+00:00
-- url     : https://prove2.me/submissions/b7018445-4f08-4f76-91ba-219cfe37ef85

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_card_hexagon
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_mid

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
theorem _root_.solution (h : SES DA NA DB NB DC NC f g) (hA : IsFin DA NA) (hC : IsFin DC NC) :
    q DB NB = q DA NA * q DC NC := by
  have hB := isFin_mid h hA hC
  have key := card_hexagon h
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  obtain ⟨_, _⟩ := hC
  have e1 : (Nat.card (T NA DA) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e2 : (Nat.card (T NB DB) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e3 : (Nat.card (T NC DC) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key' : (Nat.card (T DA NA) : ℚ) * Nat.card (T DC NC) * Nat.card (T NB DB) =
      Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC) := by exact_mod_cast key
  unfold q
  field_simp
  linarith [key']
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
