-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_resP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:51:35.019295+00:00
-- url     : https://prove2.me/submissions/26208305-7ce9-4c3d-989e-66eb9c4420aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_pullR


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
variable (p : Ideal S) [p.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    pushR G (resP p v) = spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v := by
  unfold resP
  exact pushR_pullR (R := S) (R' := Localization.AtPrime p) (G := G) _
end ReciprocityTheory.ChartRestriction.G.Chart
