-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.fromL_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:01:54.301854+00:00
-- url     : https://prove2.me/submissions/b114d938-a0f2-452c-af68-4e16e9ef2b4c

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
theorem _root_.solution : (fromL s).comp (algebraMap (DualNumber S) (Ld s)) = dAway s :=
  IsLocalization.lift_comp _
end ReciprocityTheory.ChartRestriction.G.Chart
