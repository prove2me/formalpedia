-- Prove2me | solution 1 for P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:53.391596+00:00
-- url     : https://prove2.me/submissions/19bcdef8-9737-47a1-b09b-21334017bec4

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710


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
theorem _root_.solution (n : G) (hn : n ∈ N) (g : G) : (retr N (n * g) : G) = n * retr N g :=
  congrArg Subtype.val (retr_mul N ⟨n, hn⟩ g)
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
