-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:19.184857+00:00
-- url     : https://prove2.me/submissions/d98d44e9-928c-4f00-81bf-545aae87f4fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a + b) = gs f y U a + gs f y U b := by
  simp only [gs_eq f y U h, map_add]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
