-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:25.385039+00:00
-- url     : https://prove2.me/submissions/db4bdf08-9d36-4baa-bfc1-7d32e0e3450c

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
theorem _root_.solution (h : SES DA NA DB NB DC NC f g) (hA : IsFin DA NA) (hC : IsFin DC NC) :
    IsFin DB NB := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  exact ⟨finite_of_exact _ _ h1, finite_of_exact _ _ h4⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
