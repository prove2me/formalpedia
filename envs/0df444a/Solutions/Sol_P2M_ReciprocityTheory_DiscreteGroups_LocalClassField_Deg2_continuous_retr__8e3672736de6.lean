-- Prove2me | solution 1 for P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_continuous_retr__8e3672736de6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:16.32442+00:00
-- url     : https://prove2.me/submissions/0f8eeda2-dc48-4a72-a57d-8027bb0c9284

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution (hN : IsOpen (N : Set G)) : Continuous fun g => (retr N g : G) :=
  continuous_subtype_val.comp (continuous_retr N hN)
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
