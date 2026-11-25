-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.fromL_toL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:33:40.842168+00:00
-- url     : https://prove2.me/submissions/cb44e9af-2171-4752-8757-e9378879a04d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dAway_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_toL_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fromL_comp
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
theorem _root_.solution : (fromL s).comp (toL s) = RingHom.id _ := by
  apply dAway_ext s
  rw [RingHom.comp_assoc, toL_comp, fromL_comp, RingHom.id_comp]
end ReciprocityTheory.ChartRestriction.G.Chart
