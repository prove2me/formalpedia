-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:03:37.098838+00:00
-- url     : https://prove2.me/submissions/c4a5858f-33f1-4632-9365-d0f06ffbebff

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_ses_of_rep
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_mid
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_q_mul


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
theorem _root_.solution (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b))
    (hA : HFin ρA g) (hC : HFin ρC g) : HFin ρB g ∧ h ρB g = h ρA g * h ρC g :=
  have hs := ses_of_rep ρA ρB ρC g i p hi hip hp hiG hpG
  ⟨isFin_mid hs hA hC, q_mul hs hA hC⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
