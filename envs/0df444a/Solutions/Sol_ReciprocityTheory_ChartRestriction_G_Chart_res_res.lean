-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.res_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:37.971798+00:00
-- url     : https://prove2.me/submissions/6cd1403b-f366-407c-a93b-ec8886f18c4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
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
variable {S : Type} [CommRing S]
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j') ≫ spMap (dualMapS j) ≫ y = spMap (dualMapS (j'.comp j)) ≫ y := by
  rw [← Category.assoc, spMap_comp, dualMapS_comp]
end ReciprocityTheory.ChartRestriction.G.Chart
