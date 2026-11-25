-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scale_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:43.653216+00:00
-- url     : https://prove2.me/submissions/d2005863-a903-4b68-8190-5711c51d4dca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleS_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] (a b : A) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) a) ≫ spMap (scaleS b) ≫ y = spMap (scaleS (a * b)) ≫ y := by
  rw [← Category.assoc, spMap_comp, scaleS_comp]
end ReciprocityTheory.ChartRestriction.G.Chart
