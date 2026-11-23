-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.cub_rot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:27:46.986258+00:00
-- url     : https://prove2.me/submissions/8d629df3-6c78-4b92-85dd-a1f856bbfe46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (h : IsCub θ) (x y z : A) : θ x y z = θ y z x := by
  exact (h.s01 x y z).trans (h.s12 y x z)
end ReciprocityTheory.ChartRestriction.G.H1
