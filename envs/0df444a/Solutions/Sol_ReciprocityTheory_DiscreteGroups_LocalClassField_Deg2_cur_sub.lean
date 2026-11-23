-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.cur_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:04.354873+00:00
-- url     : https://prove2.me/submissions/7f926f41-958e-411d-aba3-3ca2bcb171a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq

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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution (M : TRep R G) (x x' : M.coch.X 2) (g h : G) :
    cur M (x - x') g h = cur M x g h - cur M x' g h := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
