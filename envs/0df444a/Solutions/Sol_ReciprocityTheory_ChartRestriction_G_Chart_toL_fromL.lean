-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.toL_fromL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:37.284981+00:00
-- url     : https://prove2.me/submissions/59cc5e3e-9ddc-4908-ab5b-f5411c17a14b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
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
theorem _root_.solution : (toL s).comp (fromL s) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (TrivSqZeroExt.inl s : DualNumber S))
  rw [RingHom.comp_assoc, fromL_comp, toL_comp, RingHom.id_comp]
end ReciprocityTheory.ChartRestriction.G.Chart
