-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scale_pow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:00:17.012803+00:00
-- url     : https://prove2.me/submissions/07206b43-4811-466c-ae11-b0a4d07c2bf4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_scale


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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] (x : A) (a b : ℕ) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) (x ^ a)) ≫ spMap (scaleS (x ^ b)) ≫ y = spMap (scaleS (x ^ (a + b))) ≫ y := by
  rw [scale_scale, pow_add]
end ReciprocityTheory.ChartRestriction.G.Chart
