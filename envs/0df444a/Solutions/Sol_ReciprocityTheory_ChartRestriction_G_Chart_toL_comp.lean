-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.toL_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:09:32.262149+00:00
-- url     : https://prove2.me/submissions/8e752c47-1a44-4db7-8abe-2b2e834ca661

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {S : Type} [CommRing S] (s : S)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution : (toL s).comp (dAway s) = algebraMap (DualNumber S) (Ld s) :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose_spec
end ReciprocityTheory.ChartRestriction.G.Chart
