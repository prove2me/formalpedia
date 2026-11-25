-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.ses_of_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:07.582086+00:00
-- url     : https://prove2.me/submissions/9b16bf81-d426-4953-91b9-1a8ec43d9561

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_nHom
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_nHom_dHom
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_map_dHom
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_map_nHom

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
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b)) :
    SES (dHom ρA g) (nHom ρA) (dHom ρB g) (nHom ρB) (dHom ρC g) (nHom ρC) i p :=
  ⟨hi, hip, hp, map_dHom ρA ρB g i hiG, map_nHom ρA ρB i hiG, map_dHom ρB ρC g p hpG,
    map_nHom ρB ρC p hpG, dHom_nHom ρB g, nHom_dHom ρB g⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
