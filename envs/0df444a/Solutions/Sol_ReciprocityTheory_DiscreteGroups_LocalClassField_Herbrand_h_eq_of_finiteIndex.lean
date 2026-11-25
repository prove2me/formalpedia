-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_eq_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:48.939314+00:00
-- url     : https://prove2.me/submissions/bd1ae952-0514-40d4-a90f-384e472025cb

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_iff_of_finiteIndex
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_q_eq_of_finiteIndex
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
theorem _root_.solution (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hi : Injective i) (hfi : i.range.FiniteIndex) (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) :
    (HFin ρA g ↔ HFin ρB g) ∧ (HFin ρA g → h ρA g = h ρB g) :=
  ⟨isFin_iff_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g),
    q_eq_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g)⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
