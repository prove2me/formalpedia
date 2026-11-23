-- Prove2me | solution 1 for P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:51.51103+00:00
-- url     : https://prove2.me/submissions/ed2bacd4-33fe-45bd-8b1a-bb3d2fa305ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b


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
theorem _root_.solution (n : G) (hn : n ∈ N) (g : G) : rep N (n * g) = rep N g := rep_mul N ⟨n, hn⟩ g
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
