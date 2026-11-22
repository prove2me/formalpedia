-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:15.460678+00:00
-- url     : https://prove2.me/submissions/a67b8efb-71a3-4d79-b7a0-41fb92fccd07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace IsGrpPullback
theorem _root_.solution {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f f' : S' ⟶ S} {φ φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (e : f = f') (e' : φ = φ') : IsGrpPullback G' G f' φ' := by
  subst e e'
  exact h
end IsGrpPullback
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
