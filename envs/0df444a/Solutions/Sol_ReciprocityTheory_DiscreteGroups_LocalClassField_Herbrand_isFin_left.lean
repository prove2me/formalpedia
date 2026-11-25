-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:31.070359+00:00
-- url     : https://prove2.me/submissions/81c7e4ea-8df2-4b21-9278-fd53504cdfbd

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_SES_swap
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_half_hexagon
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_finite_of_exact

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
theorem _root_.solution (h : SES DA NA DB NB DC NC f g) (hB : IsFin DB NB) (hC : IsFin DC NC) :
    IsFin DA NA := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  obtain ⟨_, _⟩ := hB
  obtain ⟨_, _⟩ := hC
  exact ⟨finite_of_exact _ _ h6, finite_of_exact _ _ h3⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
