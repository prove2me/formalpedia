-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.away_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:17.906446+00:00
-- url     : https://prove2.me/submissions/9dfdac06-3943-4a2f-9c1b-7b3d6c7be068

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (u : S) : IsUnit (algebraMap S (Localization.Away u) u) :=
  IsLocalization.Away.algebraMap_isUnit u
end ReciprocityTheory.ChartRestriction.G.Chart
