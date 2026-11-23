-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.nHom_dHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:30.927729+00:00
-- url     : https://prove2.me/submissions/45770bdd-ebe1-4fbc-8f77-e4fbbd9090f2

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB

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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (ρ : Representation k G M) (g : G) (x : M) : nHom ρ (dHom ρ g x) = 0 := by
  change ρ.norm (ρ g x - x) = 0
  rw [map_sub, Representation.norm_self_apply, sub_self]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
