-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.card_hexagon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:26.190027+00:00
-- url     : https://prove2.me/submissions/1bf4dc92-c30b-493a-85f3-e130924c4eee

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_SES_swap
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_half_hexagon
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_card_six

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
    Nat.card (T DA NA) * Nat.card (T DC NC) * Nat.card (T NB DB) =
      Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC) := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  exact card_six _ _ _ _ _ _ h1 h2 h3 h4 h5 h6
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
