-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff_tanS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:53.186187+00:00
-- url     : https://prove2.me/submissions/06e7470a-9193-463b-a254-374a7db66b68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap


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
theorem _root_.solution (w : sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p) :
    IsTan w ↔ TanS (pushR G w) := by
  unfold IsTan TanS
  constructor
  · intro h
    have h' := congrArg (pushR G) h
    rw [pushR_spMap, pushR_one] at h'
    exact h'
  · intro h
    apply pushR_inj (G := G)
    rw [pushR_spMap, pushR_one]
    exact h
end ReciprocityTheory.ChartRestriction.G.Chart
