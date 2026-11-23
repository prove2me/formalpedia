-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.d_sub_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:49.387807+00:00
-- url     : https://prove2.me/submissions/910715ce-b78f-4788-807c-706b3b7b9d64

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
theorem _root_.solution (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) (w : M.coch.X 1) :
    M.coch.d 2 (x - M.coch.d 1 w) = 0 := by
  rw [map_sub, hx, M.coch.dd, sub_zero]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
