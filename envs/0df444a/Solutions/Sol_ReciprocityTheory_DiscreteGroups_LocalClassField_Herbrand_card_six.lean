-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.card_six
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:02.630533+00:00
-- url     : https://prove2.me/submissions/17605bcd-c877-496c-a2bf-5158ac6143e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_card_eq_ker_mul_range

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
variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution {X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [AddCommGroup X₄] [AddCommGroup X₅] [AddCommGroup X₆] (f₁ : X₁ →+ X₂) (f₂ : X₂ →+ X₃)
    (f₃ : X₃ →+ X₄) (f₄ : X₄ →+ X₅) (f₅ : X₅ →+ X₆) (f₆ : X₆ →+ X₁) (h₁ : f₂.ker = f₁.range)
    (h₂ : f₃.ker = f₂.range) (h₃ : f₄.ker = f₃.range) (h₄ : f₅.ker = f₄.range)
    (h₅ : f₆.ker = f₅.range) (h₆ : f₁.ker = f₆.range) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ = Nat.card X₂ * Nat.card X₄ * Nat.card X₆ := by
  rw [card_eq_ker_mul_range f₁, card_eq_ker_mul_range f₂, card_eq_ker_mul_range f₃,
    card_eq_ker_mul_range f₄, card_eq_ker_mul_range f₅, card_eq_ker_mul_range f₆, h₁, h₂, h₃, h₄, h₅, h₆]
  ring
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
