-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.chart_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:33.449436+00:00
-- url     : https://prove2.me/submissions/735f28cb-4f0e-4a40-b83d-94897931e798

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (c : A) (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (scaleS (S := S) c) ≫ pushR G (pt C h) = pushR G (pt C ((scaleS c).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2
end ReciprocityTheory.ChartRestriction.G.Chart
