-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.finite_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:48.312971+00:00
-- url     : https://prove2.me/submissions/6440c23a-fef3-4681-ac0c-55a969c1eb47

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
theorem _root_.solution (φ : X →+ Y) (ψ : Y →+ Z) (hex : ψ.ker = φ.range) [Finite X] [Finite Z] :
    Finite Y := by
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_ker_mul_range ψ, hex]
  have : Finite φ.range := Set.finite_range φ
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
