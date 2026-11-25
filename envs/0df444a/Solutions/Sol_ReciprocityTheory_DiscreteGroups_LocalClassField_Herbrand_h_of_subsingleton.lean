-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:11.566376+00:00
-- url     : https://prove2.me/submissions/7395a6df-6a99-4d80-8a4d-b3b9647e2362

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_eq

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
variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]
variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (ρ : Representation k G M) (g : G) [Subsingleton (TateZerothCohomology ρ g)]
    [Subsingleton (H1 ρ g)] : HFin ρ g ∧ h ρ g = 1 := by
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rw [h_eq, Nat.card_of_subsingleton (0 : TateZerothCohomology ρ g), Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
